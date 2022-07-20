module Experiment.Steel.Effect

module U  = Learn.Util
module M  = Experiment.Steel.Repr.M
module C  = Experiment.Steel.Combinators
module T  = FStar.Tactics
module L  = FStar.List.Pure
module UV = Learn.Universe
module SE = Steel.Effect
module SH = Experiment.Steel.Steel

open Experiment.Steel.Interface

#push-options "--ide_id_info_off"

irreducible let __mrepr_implicit__ : unit = ()


(**** MRepr effect *)

/// We fix the universe [u#p] of the types in bind_pure to [u#8].
/// Values in lower universes are raised.
/// We observe some bind pure with universes 2 because of Steel' req_t, ens_t...
/// ALT? take the maximum of the universes that appear in the goals.

unfold
type prog_tree = M.prog_tree u#a u#8

type repr' (a : Type) (t : M.prog_tree u#a u#p a) : Type
  = r : M.repr u#a u#p SH.KSteel a { r.repr_tree == t }

type repr (a : Type) (t : prog_tree u#a a) : Type
  = r : M.repr u#a u#8 SH.KSteel a { r.repr_tree == t }

let return_
      (a : Type) (x : a)
  : repr u#a a (M.Tret a x (fun _ -> []))
  = C.return #a x

(***** bind *)

[@@ __repr_M__]
noeq inline_for_extraction
type combine_bind_t
       (a : Type u#a) (b : Type u#b)
       (f : prog_tree a) (g : a -> prog_tree b)
= {
  cb_bind_repr : prog_tree b;
  cb_bind_impl : (rf : repr a f) -> (rg : ((x : a) -> repr b (g x))) ->
                 repr b cb_bind_repr
}

[@@ __repr_M__]
inline_for_extraction
let combine_bind
      (a : Type u#b) (b : Type u#b) 
      (f : prog_tree a) (g : a -> prog_tree b)
  : combine_bind_t a b f g
  = {
    cb_bind_repr = M.Tbind a b f (fun x -> g x); // We need the functional extensionality so we eta-expend g
    cb_bind_impl = (fun rf rg ->
                      U.funext_eta (fun x -> g x) (fun x -> (rg x).repr_tree)
                        (U.by_refl ()) (U.by_refl ())
                        (fun x -> ());
                      C.bind #a #b rf rg);
  }

/// Since we want to represent the program as a tree, we need [u#a == u#b]. However when defining an effect,
/// F* requires the bind combinator to be polymorphic in the two universes ([u#a -> u#b -> u#b]).
/// To work around this restriction, we declare the bind combinator with the signature expected by F*,
/// but the actual combination is made by an argument which is solved by tactic, by applying
/// our restricted combinator [combine_bind].
/// The tactic will fail if [u#a <> u#b].
let bind_
      (a : Type u#a) (b : Type u#b)
      (#f : prog_tree a) (#g : a -> prog_tree b)
      (#[@@@ __mrepr_implicit__] cb
        : (f : prog_tree a) -> (g : (a -> prog_tree b)) -> combine_bind_t a b f g)
      (rf : repr u#a a f) (rg : (x : a) -> repr u#b b (g x))
  : repr u#b b (cb f g).cb_bind_repr
  = (cb f g).cb_bind_impl rf rg


(***** subcomp *)

type combine_subcomp_t
      (a : Type u#a) (f : prog_tree a) (g : prog_tree a)
  = repr a f -> repr a g

let combine_subcomp_refl
      (a : Type u#a) (f : prog_tree a)
  : combine_subcomp_t a f f
  = fun rf -> rf

let subcomp
      (a : Type u#a)
      (#f : prog_tree a) (#g : prog_tree a)
      (#[@@@ __mrepr_implicit__] cb : combine_subcomp_t a f g)
      (rf : repr a f)
  : repr a g
  = cb rf


(***** if then else *)

let if_then_else
      (a : Type)
      (#thn : prog_tree a) (#els : prog_tree a)
      (rthn : repr a thn) (rels : repr a els)
      (guard : bool)
  : Type
  = repr a (M.Tif a guard thn els)

let ite_combine_thn
      (a : Type) (guard : bool) (thn els : prog_tree a)
      (_ : squash guard)
  : combine_subcomp_t a thn (M.Tif a guard thn els)
  = fun rthn -> {
    repr_tree  = M.Tif a guard thn els;
    repr_steel = (fun pre0 post0 c ->
                    let M.TCif pre post cthn cels = c in
                    C.ite_steel_thn a guard thn els pre post cthn cels (rthn.repr_steel _ _ cthn) ())
  }

let ite_combine_els
      (a : Type) (guard : bool) (thn els : prog_tree a)
      (_ : squash (~guard))
  : combine_subcomp_t a els (M.Tif a guard thn els)
  = fun rels -> {
    repr_tree  = M.Tif a guard thn els;
    repr_steel = (fun pre0 post0 c ->
                    let M.TCif pre post cthn cels = c in
                    C.ite_steel_els a guard thn els pre post cthn cels (rels.repr_steel _ _ cels) ())
  }


irreducible let __ite_soundness__ : unit = ()

[@@ resolve_implicits; __ite_soundness__]
let ite_soundness_tac () : T.Tac unit
  = T.(
    iterAll (fun () -> try trefl () with _ -> ());
    norm [delta_only [`%pure_null_wp0]; simplify]; trivial ();
    first [(fun () -> apply (`ite_combine_thn)); (fun () -> apply (`ite_combine_els))];
    smt ()
  )


[@@ ite_soundness_by __ite_soundness__]
total reflectable effect {
  MRepr (a : Type) (r : prog_tree a)
  with {
    repr;
    return = return_;
    bind = bind_;
    subcomp;
    if_then_else
  }
}

let return (#a : Type u#a) (x : a)
  : MRepr a (M.Tret a x (fun _ -> []))
  = MRepr?.reflect (return_ a x)


(***** bind (PURE, MRepr) |> MRepr *)

[@@ __repr_M__]
noeq inline_for_extraction
type combine_bind_pure_t
       (a : Type u#r) (b : Type u#a)
       (wp : pure_wp a) (g : a -> M.prog_tree u#a u#p b)
= {
  cb_bindP_repr : M.prog_tree u#a u#p b;
  cb_bindP_impl : (rf : unit -> PURE a wp) -> (rg : ((x : a) -> repr' b (g x))) ->
                  repr' u#a u#p b cb_bindP_repr
}

/// This should be applied with [u#r <= u#8] so [u#(max r 8) = u#8]
[@@ __repr_M__]
inline_for_extraction
let combine_bind_pure
      (a : Type u#r) (b : Type u#a)
      (wp : pure_wp a) (g : a -> M.prog_tree u#a u#(max r 8) b)
      
  : combine_bind_pure_t u#r u#a u#(max r 8) a b wp g
  = 
    let t = M.TbindP (UV.raise_t u#r u#8 a) b
                     (UV.raise_pure_wp u#r u#8 wp) (UV.lift_dom g) in
  {
    cb_bindP_repr = t;
    cb_bindP_impl = (fun rf rg ->
                       let rg' = UV.lift_dom rg in
                       let r = C.bindP #(UV.raise_t u#r u#8 a) #b (UV.raise_pure_wp u#r u#8 wp)
                                       (UV.raise_pure_val wp rf) rg'
                       in
                       U.funext_eta (UV.lift_dom g) (fun x -> (rg' x).repr_tree)
                         (U.by_refl ()) (U.by_refl ())
                         (fun x -> ());
                       assert (r.repr_tree == t)
                         by T.(norm [delta_only [`%M.Mkrepr?.repr_tree]];
                               norm [delta_only [`%C.bindP]; iota];
                               smt ());
                       r)
  }

let bind_pure_mrepr
      (a : Type u#r) (b : Type u#a)
      (#wp : pure_wp a)
      (#g : a -> prog_tree b)
      (#[@@@ __mrepr_implicit__] cb
        : (wp : pure_wp a) -> (g : (a -> prog_tree b)) -> combine_bind_pure_t u#r u#a u#8 a b wp g)
      (rf : eqtype_as_type unit -> PURE a wp)
      (rg : (x : a) -> repr b (g x))
  : repr b (cb wp g).cb_bindP_repr
  = (cb wp g).cb_bindP_impl rf rg

#push-options "--warn_error -330"
polymonadic_bind (PURE, MRepr) |> MRepr = bind_pure_mrepr
#pop-options


(***** lifting Steel.Effect.SteelBase ~> MRepr *)

/// The sub_effect is not working (order of resolution of the implicits, use of Steel's combinators instead of
/// MRepr's combinators, Steel computation unexpectedly lifted where MRepr does not appear).
/// One has use an explicit cast ([call]) instead.

(*
let lift_steel_mrepr
      (a : Type) (pre : SE.pre_t) (post : SE.post_t a)
      (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      (f : Steel.Effect.repr a false pre post req ens)
  : repr a M.(Tspec a (spec_r_steel u#a u#8 pre post req ens))
  = C.repr_of_steel #a pre post req ens
      (fun () -> SE.SteelBase?.reflect f)
  
sub_effect Steel.Effect.SteelBase ~> MRepr = lift_steel_mrepr
*)

unfold
let call (#b : Type u#b)
      (#a : b -> Type) (#pre : b -> SE.pre_t) (#post : (x : b) -> SE.post_t (a x))
      (#req : (x : b) -> SE.req_t (pre x)) (#ens : (x : b) -> SE.ens_t (pre x) (a x) (post x))
      ($f : (x : b) -> SE.Steel (a x) (pre x) (post x) (req x) (ens x)) (x : b)
  : MRepr (a x) (M.Tspec (a x) (M.spec_r_steel u#a u#8 (pre x) (post x) (req x) (ens x)))
  = MRepr?.reflect (C.repr_of_steel #(a x) (pre x) (post x) (req x) (ens x) (fun () -> f x))


(**** Conversion to Steel *)

/// [ConvEffect] is a dummy effect whose only purpose is to avoid the retypechecking of [prog_tree] that would
/// happen if it appeared outside effect combinators.

type cv_repr (a : Type u#a) (pre : SE.pre_t) (post : SE.post_t a)
             (req : SE.req_t pre) (ens : SE.ens_t pre a post)
             (flags : list flag)
  : Type
  = SH.unit_steel a pre post req ens

/// [ConvEffect] is only used to convert a [MRepr] into a [SH.unit_steel]. Its combinators (return, bind,
/// lifting of pure) should never be used.

irreducible let __cv_unused__ : unit = ()

[@@ resolve_implicits; __cv_unused__]
let cv_unused_tac () : T.Tac unit
  = T.fail "cv_unused"

[@@ erasable]
noeq type cv_unused =

let elim_cv_unused (#a : Type) (u : cv_unused) : a
  = match u with

unfold let dummy_cv (a : Type u#a) = cv_repr a SE.emp (fun _ -> SE.emp) (fun _ -> True) (fun _ _ _ -> True) []

let cv_return
      (a : Type u#a) (x : a) (#[@@@ __cv_unused__] u : cv_unused)
  : dummy_cv a
  = elim_cv_unused u

let cv_bind
      (a : Type u#a) (b : Type u#b)
      (#pre_f : SE.pre_t) (#post_f : SE.post_t a)
      (#req_f : SE.req_t pre_f) (#ens_f : SE.ens_t pre_f a post_f)
      (#fsf : list flag)
      (#pre_g : a -> SE.pre_t) (#post_g : a -> SE.post_t b)
      (#req_g : (x : a) -> SE.req_t (pre_g x)) (#ens_g : (x : a) -> SE.ens_t (pre_g x) b (post_g x))
      (#fsg : (x : a) -> list flag)
      (#[@@@ __cv_unused__] u : cv_unused)
      (f : cv_repr a pre_f post_f req_f ens_f fsf)
      (g : (x : a) -> cv_repr b (pre_g x) (post_g x) (req_g x) (ens_g x) (fsg x))
  : dummy_cv b
  = elim_cv_unused u

/// We need the reification for extracting the Steel representation and [lift_mrepr_cv] has [t : prog_tree a]
/// as an informative binder. (ALT? make [prog_tree] erasable)
[@@ allow_informative_binders]
total reifiable effect {
  ConvEffect
    (a : Type) (pre : SE.pre_t) (post : SE.post_t a)
    (req : SE.req_t pre) (ens : SE.ens_t pre a post)
    (flags : list flag)
  with {
    repr   = cv_repr;
    return = cv_return;
    bind   = cv_bind;
  }
}


let lift_pure_cv
      (a : Type) (wp : pure_wp a)
      (#[@@@ __cv_unused__] u : cv_unused)
      (f : (eqtype_as_type unit) -> PURE a wp)
  : Tot (dummy_cv a)
  = elim_cv_unused u

sub_effect PURE ~> ConvEffect = lift_pure_cv



noeq
type mrepr_to_steel_t
       (flags : list flag)
       (a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
       (t : prog_tree a)
  = | MReprToSteel of (repr a t -> SH.unit_steel a pre post req ens)

let lift_mrepr_cv
      (a : Type) (t : prog_tree a)
      (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post) (flags : list flag)
      ([@@@ __mrepr_implicit__] cv : mrepr_to_steel_t flags a pre post req ens t)
      (r : repr a t)
  : cv_repr a pre post req ens flags
  = let MReprToSteel cv = cv in
    cv r

sub_effect MRepr ~> ConvEffect = lift_mrepr_cv


(**** Implicits resolution *)

module ES   = Experiment.Steel
module LV   = Experiment.Steel.Repr.LV
module TcS  = Experiment.Steel.Tac

open FStar.Tactics
open Learn.Tactics.Util


private
let __build_mrepr_to_steel_norew
      (flags : list flag)
      (a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      (t : prog_tree a)
      (goal : (impl : ((pre : M.pre_t) -> (post : M.post_t a) -> (c : M.tree_cond t pre post) ->
                          M.repr_steel_t SH.KSteel a pre post (M.tree_req t c) (M.tree_ens t c))) ->
              ES.__to_steel_goal a pre post req ens M.({repr_tree = t; repr_steel = impl}))
  : mrepr_to_steel_t flags a pre post req ens t
  = MReprToSteel (fun r -> goal r.repr_steel)

/// Solves a goal [mrepr_to_steel_t flags a pre post req ens t] using [ES.build_to_steel].
let build_mrepr_to_steel_norew (fr : flags_record) : Tac unit
  =
    apply (`__build_mrepr_to_steel_norew);
    let impl = intro () in
    //exact (`((_ by (ES.build_to_steel (make_flags_record (`#flags)))) <: (`#(cur_goal ()))))
    ES.build_to_steel fr


private
let __build_mrepr_to_steel_wrew
      (flags : list flag)
      (a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      (t : prog_tree a)
      (goal_tr : M.to_repr_t a pre post req ens)
      (goal_sp : ES.to_steel_goal_spec a goal_tr.r_pre goal_tr.r_post goal_tr.r_req goal_tr.r_ens t)
  : mrepr_to_steel_t flags a pre post req ens t
  = MReprToSteel (fun r ->
      M.steel_of_repr goal_tr
        (let lc1 = LV.lc_sub_push goal_sp.goal_spec_LV in
         ES.prog_LV_to_Fun_extract_wp r goal_sp.goal_spec_LV lc1 ()
            goal_tr.r_req goal_tr.r_ens (fun sl0 -> goal_sp.goal_spec_WP)))

/// Solves a goal [mrepr_to_steel_t flags a pre post req ens t] using a [rewrite_with_tactic] to avoid
/// normalizing the WP twice.
let build_mrepr_to_steel_wrew (fr : flags_record) (flags : list flag) : Tac unit
  =
    let fr    = make_flags_record flags in
    apply_raw (`__build_mrepr_to_steel_wrew);

    // goal_tr
    let t = timer_start "specs     " fr.f_timer in
    TcS.build_to_repr_t fr (fun () -> [Info_location "in the specification"]);

    // goal_sp
    norm [delta_attr [`%__tac_helper__]; iota];
    let t = ES.build_to_steel_wrew fr flags t in

    timer_stop t


/// On a goal [mrepr_to_steel_t flags a pre post req ens t] returns [flags].
let collect_flags () : Tac (list flag)
  =
    let args = (collect_app (cur_goal ()))._2      in
    guard (L.length args = 7);
    unquote (L.hd args)._1

/// Solves a goal [mrepr_to_steel_t flags a pre post req ens t]
let build_mrepr_to_steel () : Tac unit
  =
    let flags = collect_flags ()        in
    let fr    = make_flags_record flags in
    if fr.f_wrew
    then build_mrepr_to_steel_wrew  fr flags
    else build_mrepr_to_steel_norew fr


[@@ resolve_implicits; __mrepr_implicit__]
let mrepr_implicits_tac () : Tac unit
  = with_policy Force (fun () ->
    
    iterAll (fun () ->
      intros' ();
      try first [
        trefl;
        (fun () -> apply (`combine_bind));
        (fun () -> apply (`combine_subcomp_refl));
        (fun () -> apply (`combine_bind_pure));
        (fun () -> // if it is an [mrepr_to_steel_t] goal, skip
                let hd = (collect_app (cur_goal ()))._1 in
                match inspect hd with
                | Tv_FVar fv | Tv_UInst fv _ ->
                  let fv = inspect_fv fv in
                  guard (implode_qn fv = (`%mrepr_to_steel_t))
                | _ -> fail "")
      ] with _ ->
        // The only sources of Fail_MRepr_implicit should be a bind where the two types involved belong to
        // different universes. Or a polymonadic bind with an universe greater than [u#8].
        TcS.cs_raise default_flags TcS.dummy_ctx (fun m -> fail (m Fail_MRepr_implicit [])));

    // At this point there should only remains a [mrepr_to_steel_t] goal
    iterAll build_mrepr_to_steel
  )


(**** Notations *)

unfold
let usteel (a : Type) (pre : SE.pre_t) (post : SE.post_t a)
          (req : SE.req_t pre) (ens : SE.ens_t pre a post)
  : Type
  = SH.unit_steel a pre post req ens

let to_steel
      (#[apply (`[])] flags : list flag)
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (r : unit -> ConvEffect a pre post req ens flags)
  : usteel a pre post req ens
  = reify (r ())
