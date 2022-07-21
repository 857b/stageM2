module Experiment.Steel.Effect

module U   = Learn.Util
module M   = Experiment.Steel.Repr.M
module C   = Experiment.Steel.Combinators
module T   = FStar.Tactics
module L   = FStar.List.Pure
module UV  = Learn.Universe
module SE  = Steel.Effect
module SA  = Steel.Effect.Atomic
module SH  = Experiment.Steel.Steel
module Mem = Steel.Memory

open Experiment.Steel.Interface

#push-options "--ide_id_info_off"

irreducible let __mrepr_implicit__ : unit = ()


(*** MRepr effect *)

/// We fix the universe [u#p] of the types in bind_pure to [u#8].
/// Values in lower universes are raised.
/// We observe some bind pure with universes 2 because of Steel' req_t, ens_t...
/// ALT? take the maximum of the universes that appear in the goals.

unfold
type prog_tree = M.prog_tree u#a u#8

type repr' (a : Type) (ek : SH.effect_kind) (t : M.prog_tree u#a u#p a) : Type
  = r : M.repr u#a u#p ek a { r.repr_tree == t }

type repr (a : Type) (ek : SH.effect_kind) (t : prog_tree u#a a) : Type
  = r : M.repr u#a u#8 ek a { r.repr_tree == t }


(***** return *)

let return_ghostI
      (a : Type) (x : a) (#opened: Mem.inames)
  : repr u#a a (SH.KGhostI opened) (M.Tret a x (fun _ -> []))
  = C.return_ghostI_hint #a x (fun _ -> [])

let return_ghost
      (a : Type) (x : a) (#opened: Mem.inames)
  : repr u#a a (SH.KGhost opened) (M.Tret a x (fun _ -> []))
  = C.return_ghost #a x

// FIXME
//   if we replace SH.KGhostI by SH.KGhost, [test3'] fails because of some bind
//   maybe we can infer when one should use return_ghostI/return_ghost
let return_
      (a : Type) (x : a) (#[@@@ __mrepr_implicit__] opened: Mem.inames)
  : repr u#a a (SH.KGhostI opened) (M.Tret a x (fun _ -> []))
  = return_ghostI a x #opened

(***** bind *)

[@@ __repr_M__]
noeq inline_for_extraction
type combine_bind_t
       (a : Type u#a) (b : Type u#b)
       (ek0 ek1 ek : SH.effect_kind)
       (f : prog_tree a) (g : a -> prog_tree b)
= {
  cb_bind_repr : prog_tree b;
  cb_bind_impl : (rf : repr a ek0 f) -> (rg : ((x : a) -> repr b ek1 (g x))) ->
                 repr b ek cb_bind_repr
}

type combinable_bind_repr (a0 a1 : Type u#a) (ek0 ek1 ek2 : SH.effect_kind)
  = (f : M.repr u#a u#8 ek0 a0) -> (g : ((x : a0) -> M.repr u#a u#8 ek1 a1)) ->
    repr a1 ek2 (M.Tbind a0 a1 f.repr_tree (fun x -> (g x).repr_tree))

noeq inline_for_extraction
type combinable_bind_t (a0 a1 : Type u#a) (ek0 ek1 ek2 : SH.effect_kind) = {
  cba_bind_ek0'  : SH.effect_kind;
  cba_bind_ek1'  : SH.effect_kind;
  cba_bind_repr  : combinable_bind_repr a0 a1 cba_bind_ek0' cba_bind_ek1' ek2;
  cba_bind_lift0 : C.steel_liftable a0 ek0 cba_bind_ek0';
  cba_bind_lift1 : C.steel_liftable a1 ek1 cba_bind_ek1';
}

[@@ __repr_M__]
inline_for_extraction
let combine_bind
      (a : Type u#b) (b : Type u#b)
      (ek0 ek1 ek2 : SH.effect_kind)
      (cba : combinable_bind_t a b ek0 ek1 ek2)
      (f : prog_tree a) (g : a -> prog_tree b)
  : combine_bind_t a b ek0 ek1 ek2 f g
  = {
    cb_bind_repr = M.Tbind a b f (fun x -> g x); // We need the functional extensionality so we eta-expend g
    cb_bind_impl = (fun rf rg ->
                      let rf' = C.repr_lift cba.cba_bind_lift0 rf             in
                      let rg' (x : a) = C.repr_lift cba.cba_bind_lift1 (rg x) in
                      U.funext_eta (fun x -> g x) (fun x -> (rg' x).repr_tree)
                        (U.by_refl ()) (U.by_refl ())
                        (fun x -> ());
                      cba.cba_bind_repr rf' rg');
  }

/// Since we want to represent the program as a tree, we need [u#a == u#b]. However when defining an effect,
/// F* requires the bind combinator to be polymorphic in the two universes ([u#a -> u#b -> u#b]).
/// To work around this restriction, we declare the bind combinator with the signature expected by F*,
/// but the actual combination is made by an argument which is solved by tactic, by applying
/// our restricted combinator [combine_bind].
/// The tactic will fail if [u#a <> u#b].
let bind_
      (a : Type u#a) (b : Type u#b)
      (#ek0 #ek1 #ek : SH.effect_kind)
      (#f : prog_tree a) (#g : a -> prog_tree b)
      (#[@@@ __mrepr_implicit__] cb
        : (f : prog_tree a) -> (g : (a -> prog_tree b)) -> combine_bind_t a b ek0 ek1 ek f g)
      (rf : repr u#a a ek0 f) (rg : (x : a) -> repr u#b b ek1 (g x))
  : repr u#b b ek (cb f g).cb_bind_repr
  = (cb f g).cb_bind_impl rf rg


(***** subcomp *)

type combine_subcomp_t
      (a : Type u#a) (ek0 ek1 : SH.effect_kind) (f : prog_tree a) (g : prog_tree a)
  = repr a ek0 f -> repr a ek1 g

// TODO?: allow lifting effect_kind
let combine_subcomp_refl
      (a : Type u#a) (ek : SH.effect_kind) (f : prog_tree a)
  : combine_subcomp_t a ek ek f f
  = fun rf -> rf

let subcomp
      (a : Type u#a)
      (#ek0 : SH.effect_kind) (#ek1 : SH.effect_kind)
      (#f : prog_tree a) (#g : prog_tree a)
      (#[@@@ __mrepr_implicit__] cb : combine_subcomp_t a ek0 ek1 f g)
      (rf : repr a ek0 f)
  : repr a ek1 g
  = cb rf


(***** if then else *)

noeq
type combinable_ite_t (a : Type) (ek0 ek1 ek2 : SH.effect_kind) = {
  cba_ite_restr : squash (~ (SH.KAtomic? ek2)); // We match the restriction of SteelAtomic, but we do not need it
  cba_ite_lift0 : C.steel_liftable a ek0 ek2;
  cba_ite_lift1 : C.steel_liftable a ek1 ek2;
}

let if_then_else
      (a : Type)
      (#ek0 #ek1 #ek2 : SH.effect_kind)
      (#thn : prog_tree a) (#els : prog_tree a)
      (#[@@@ __mrepr_implicit__] cb : combinable_ite_t a ek0 ek1 ek2)
      (rthn : repr a ek0 thn) (rels : repr a ek1 els)
      (guard : bool)
  : Type
  = repr a ek2 (M.Tif a guard thn els)


inline_for_extraction noextract
let ite_steel_thn
      (a : Type) (ek : SH.effect_kind) (guard : bool) (thn : M.prog_tree a) (els : M.prog_tree a)
      (pre : M.pre_t) (post : M.post_t a) (cthn : M.tree_cond thn pre post) (cels : M.tree_cond els pre post)
      ($rthn : M.repr_steel_t ek a pre post (M.tree_req thn cthn) (M.tree_ens thn cthn))
      (_ : squash guard)
  : (let c = M.TCif #a #guard #thn #els pre post cthn cels in
     M.repr_steel_t ek a pre post (M.tree_req _ c) (M.tree_ens _ c))
  = M.repr_steel_subcomp ek _ _ _ _ (fun _ -> ()) (fun _ _ _ -> ()) rthn

inline_for_extraction noextract
let ite_steel_els
      (a : Type) (ek : SH.effect_kind) (guard : bool) (thn : M.prog_tree a) (els : M.prog_tree a)
      (pre : M.pre_t) (post : M.post_t a) (cthn : M.tree_cond thn pre post) (cels : M.tree_cond els pre post)
      ($rels : M.repr_steel_t ek a pre post (M.tree_req els cels) (M.tree_ens els cels))
      (_ : squash (~ guard))
  : (let c = M.TCif #a #guard #thn #els pre post cthn cels in
     M.repr_steel_t ek a pre post (M.tree_req _ c) (M.tree_ens _ c))
  = M.repr_steel_subcomp ek _ _ _ _ (fun _ -> ()) (fun _ _ _ -> ()) rels


let ite_combine_thn
      (a : Type) (ek0 ek1 : SH.effect_kind) (guard : bool) (thn els : prog_tree a)
      (_ : squash guard)
      (l : C.steel_liftable a ek0 ek1)
  : combine_subcomp_t a ek0 ek1 thn (M.Tif a guard thn els)
  = fun rthn -> {
    repr_tree  = M.Tif a guard thn els;
    repr_steel = (fun pre0 post0 c ->
                    let M.TCif pre post cthn cels = c in
                    ite_steel_thn a ek1 guard thn els pre post cthn cels
                         ((C.repr_lift l rthn).repr_steel _ _  cthn) ())
  }

let ite_combine_els
      (a : Type) (ek0 ek1 : SH.effect_kind) (guard : bool) (thn els : prog_tree a)
      (_ : squash (~guard))
      (l : C.steel_liftable a ek0 ek1)
  : combine_subcomp_t a ek0 ek1 els (M.Tif a guard thn els)
  = fun rels -> {
    repr_tree  = M.Tif a guard thn els;
    repr_steel = (fun pre0 post0 c ->
                    let M.TCif pre post cthn cels = c in
                    ite_steel_els a ek1 guard thn els pre post cthn cels
                          ((C.repr_lift l rels).repr_steel _ _ cels) ())
  }


private irreducible
let __ite_soundness__ : unit = ()

[@@ resolve_implicits; __ite_soundness__]
let ite_soundness_tac () : T.Tac unit
  = T.(
    let exact_hyp () =
      first (map (fun (b : binder) () -> exact b <: Tac unit) (cur_binders ()))
    in
    iterAll (fun () -> try trefl () with _ -> ());
    norm [delta_only [`%pure_null_wp0]; simplify]; trivial ();
    first [(fun () -> apply (`ite_combine_thn)); (fun () -> apply (`ite_combine_els))];
    smt ();
    first [
      (fun () -> apply (`Mkcombinable_ite_t?.cba_ite_lift0); exact_hyp ());
      (fun () -> apply (`Mkcombinable_ite_t?.cba_ite_lift1); exact_hyp ())
    ]
  )


[@@ ite_soundness_by __ite_soundness__]
total reflectable effect {
  MRepr (a : Type) (ek : SH.effect_kind) (r : prog_tree a)
  with {
    repr;
    return = return_;
    bind = bind_;
    subcomp;
    if_then_else
  }
}

let return (#a : Type u#a) (#opened : Mem.inames) (x : a)
  : MRepr a (SH.KGhostI opened) (M.Tret a x (fun _ -> []))
  = MRepr?.reflect (return_ghostI a x #opened)

let return_g (#a : Type u#a) (#opened : Mem.inames) (x : a)
  : MRepr a (SH.KGhost opened) (M.Tret a x (fun _ -> []))
  = MRepr?.reflect (return_ghost a x #opened)


(***** bind (PURE, MRepr) |> MRepr *)

[@@ __repr_M__]
noeq inline_for_extraction
type combine_bind_pure_t
       (a : Type u#r) (b : Type u#a)
       (ek : SH.effect_kind)
       (wp : pure_wp a) (g : a -> M.prog_tree u#a u#p b)
= {
  cb_bindP_repr : M.prog_tree u#a u#p b;
  cb_bindP_impl : (rf : unit -> PURE a wp) -> (rg : ((x : a) -> repr' b ek (g x))) ->
                  repr' u#a u#p b ek cb_bindP_repr
}

/// This should be applied with [u#r <= u#8] so [u#(max r 8) = u#8]
[@@ __repr_M__]
inline_for_extraction
let combine_bind_pure
      (a : Type u#r) (b : Type u#a)
      (ek : SH.effect_kind)
      (wp : pure_wp a) (g : a -> M.prog_tree u#a u#(max r 8) b)
      
  : combine_bind_pure_t u#r u#a u#(max r 8) a b ek wp g
  = 
    let t = M.TbindP (UV.raise_t u#r u#8 a) b
                     (UV.raise_pure_wp u#r u#8 wp) (UV.lift_dom g) in
  {
    cb_bindP_repr = t;
    cb_bindP_impl = (fun rf rg ->
                       let rg' = UV.lift_dom rg in
                       let r = C.bindP_ek #(UV.raise_t u#r u#8 a) #b ek (UV.raise_pure_wp u#r u#8 wp)
                                          (UV.raise_pure_val wp rf) rg'
                       in
                       U.funext_eta (UV.lift_dom g) (fun x -> (rg' x).repr_tree)
                         (U.by_refl ()) (U.by_refl ())
                         (fun x -> ());
                       assert (r.repr_tree == t)
                         by T.(norm [delta_only [`%M.Mkrepr?.repr_tree]];
                               norm [delta_only [`%C.bindP_ek]; iota];
                               smt ());
                       r)
  }

let bind_pure_mrepr
      (a : Type u#r) (b : Type u#a)
      (#ek : SH.effect_kind)
      (#wp : pure_wp a)
      (#g : a -> prog_tree b)
      (#[@@@ __mrepr_implicit__] cb
        : (wp : pure_wp a) -> (g : (a -> prog_tree b)) -> combine_bind_pure_t u#r u#a u#8 a b ek wp g)
      (rf : eqtype_as_type unit -> PURE a wp)
      (rg : (x : a) -> repr b ek (g x))
  : repr b ek (cb wp g).cb_bindP_repr
  = (cb wp g).cb_bindP_impl rf rg

#push-options "--warn_error -330"
polymonadic_bind (PURE, MRepr) |> MRepr = bind_pure_mrepr
#pop-options


(***** lifting Steel ~> MRepr *)

/// The sub_effect is not working (order of resolution of the implicits, use of Steel's combinators instead of
/// MRepr's combinators, Steel computation unexpectedly lifted where MRepr does not appear).
/// One has use an explicit cast ([call]) instead.

(*
let lift_steel_mrepr
      (a : Type) (pre : SE.pre_t) (post : SE.post_t a)
      (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      (f : Steel.Effect.repr a false pre post req ens)
  : repr a SH.KSteel M.(Tspec a (spec_r_steel u#a u#8 pre post req ens))
  = C.repr_of_steel #a pre post req ens
      (fun () -> SE.SteelBase?.reflect f)
  
sub_effect Steel.Effect.SteelBase ~> MRepr = lift_steel_mrepr
*)

unfold
let call (#b : Type u#b)
      (#a : b -> Type) (#pre : b -> SE.pre_t) (#post : (x : b) -> SE.post_t (a x))
      (#req : (x : b) -> SE.req_t (pre x)) (#ens : (x : b) -> SE.ens_t (pre x) (a x) (post x))
      ($f : (x : b) -> SE.Steel (a x) (pre x) (post x) (req x) (ens x)) (x : b)
  : MRepr (a x) SH.KSteel (M.Tspec (a x) (M.spec_r_steel u#a u#8 (pre x) (post x) (req x) (ens x)))
  = MRepr?.reflect (C.repr_of_steel #(a x) (pre x) (post x) (req x) (ens x) (fun () -> f x))

unfold
let call_g (#b : Type u#b)
      (#a : b -> Type) (#opened : b -> Mem.inames) (#pre : b -> SE.pre_t) (#post : (x : b) -> SE.post_t (a x))
      (#req : (x : b) -> SE.req_t (pre x)) (#ens : (x : b) -> SE.ens_t (pre x) (a x) (post x))
      ($f : (x : b) -> SA.SteelGhost (a x) (opened x) (pre x) (post x) (req x) (ens x)) (x : b)
  : MRepr (a x) (SH.KGhost (opened x)) (M.Tspec (a x) (M.spec_r_steel u#a u#8 (pre x) (post x) (req x) (ens x)))
  = MRepr?.reflect (C.repr_of_steel_ghost #(a x) (pre x) (post x) (req x) (ens x) (fun () -> f x))


(*** Conversion to Steel *)

/// [ConvEffect] is a dummy effect whose only purpose is to avoid the retypechecking of [prog_tree] that would
/// happen if it appeared outside effect combinators.

type cv_repr (a : Type u#a) (ek : SH.effect_kind) (pre : SE.pre_t) (post : SE.post_t a)
             (req : SE.req_t pre) (ens : SE.ens_t pre a post)
             (flags : list flag)
  : Type
  = SH.steel a pre post req ens ek

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

unfold let dummy_cv (a : Type u#a) = cv_repr a SH.KSteel SE.emp (fun _ -> SE.emp) (fun _ -> True) (fun _ _ _ -> True) []

let cv_return
      (a : Type u#a) (x : a) (#[@@@ __cv_unused__] u : cv_unused)
  : dummy_cv a
  = elim_cv_unused u

let cv_bind
      (a : Type u#a) (b : Type u#b)
      (#ek0 #ek1 : SH.effect_kind)
      (#pre_f : SE.pre_t) (#post_f : SE.post_t a)
      (#req_f : SE.req_t pre_f) (#ens_f : SE.ens_t pre_f a post_f)
      (#fsf : list flag)
      (#pre_g : a -> SE.pre_t) (#post_g : a -> SE.post_t b)
      (#req_g : (x : a) -> SE.req_t (pre_g x)) (#ens_g : (x : a) -> SE.ens_t (pre_g x) b (post_g x))
      (#fsg : (x : a) -> list flag)
      (#[@@@ __cv_unused__] u : cv_unused)
      (f : cv_repr a ek0 pre_f post_f req_f ens_f fsf)
      (g : (x : a) -> cv_repr b ek1 (pre_g x) (post_g x) (req_g x) (ens_g x) (fsg x))
  : dummy_cv b
  = elim_cv_unused u

/// We need the reification for extracting the Steel representation and [lift_mrepr_cv] has [t : prog_tree a]
/// as an informative binder. (ALT? make [prog_tree] erasable)
[@@ allow_informative_binders]
total reifiable effect {
  ConvEffect
    (a : Type) (ek : SH.effect_kind) (pre : SE.pre_t) (post : SE.post_t a)
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
       (a : Type) (ek : SH.effect_kind)
       (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
       (t : prog_tree a)
  = | MReprToSteel of (repr a ek t -> SH.steel a pre post req ens ek)

let lift_mrepr_cv
      (a : Type) (ek0 ek1 : SH.effect_kind) (t : prog_tree a)
      (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post) (flags : list flag)
      ([@@@ __mrepr_implicit__] lt : C.steel_liftable a ek0 ek1)
      ([@@@ __mrepr_implicit__] cv : mrepr_to_steel_t flags a ek1 pre post req ens t)
      (r : repr a ek0 t)
  : cv_repr a ek1 pre post req ens flags
  = let MReprToSteel cv = cv in
    cv (C.repr_lift lt r)

sub_effect MRepr ~> ConvEffect = lift_mrepr_cv


(*** Implicits resolution *)

module ES   = Experiment.Steel
module LV   = Experiment.Steel.Repr.LV
module TcS  = Experiment.Steel.Tac

open FStar.Tactics
open Learn.Tactics.Util

// TODO: better errors

private noeq
type filter_goals_r = {
  // combinable_bind_t, combinable_ite_t
  fgoals_comb : list goal;
  // steel_liftable
  fgoals_lift : list goal;
  // mrepr_to_steel_t
  fgoals_tstl : list goal;
}

let rec mrepr_implicits_init (r : filter_goals_r) : Tac filter_goals_r
  =
    match goals () with
    | [] -> r
    | g :: _ ->
      let r =
        if not (Tv_Uvar? (goal_witness g))
        then (dismiss (); r) // the goal has already been solved
        else begin
          let hd = try collect_fvar (collect_app (goal_type g))._1
                   with _ -> fail "unexpected shape"
          in
          // The only sources of failure here should be a bind where the two types involved belong to
          // different universes. Or a polymonadic bind with an universe greater than [u#8].
          if hd = (`%combine_bind_t)
          then begin
            apply (`combine_bind);
            // combinable_bind_t
            let g = _cur_goal () in
            dismiss ();
            {r with fgoals_comb = g :: r.fgoals_comb}
          end else if hd = (`%combine_subcomp_t)
          then (apply (`combine_subcomp_refl); r)
          else if hd = (`%combine_bind_pure_t)
          then (apply (`combine_bind_pure); r)

          else if hd = (`%combinable_ite_t)
          then (dismiss (); {r with fgoals_comb = g :: r.fgoals_comb})
          else if hd = (`%C.steel_liftable)
          then (dismiss (); {r with fgoals_lift = g :: r.fgoals_lift})
          else if hd = (`%mrepr_to_steel_t)
          then (dismiss (); {r with fgoals_tstl = g :: r.fgoals_tstl})
          else if hd = (`%Mem.inames)
          then (dismiss (); r) // should be inferred as side effects of other goals
          else fail "unexpected shape"
        end
      in
      mrepr_implicits_init r


/// Solves a goal [C.steel_liftable a ek0 ek1] where the heads of [ek0] and [ek1] are known.
let rec build_steel_liftable () : Tac unit
  =
    try apply (`C.Rt1n_refl)
    with _ ->
      apply (`C.Rt1n_trans);
      // lift1
      begin
        match catch (fun () -> apply (`C.Lift_ghost_ghostI)) with
        | Inr () -> C.build_erasable_t ()
        | Inl _ ->
        try apply (`C.Lift_ghostI_atomic) with _ ->
        try apply (`C.Lift_atomic_steel)  with _ ->
        fail "build_steel_liftable"
      end;

      build_steel_liftable ()
  

private
type effect_kind_enum = | ESteel | EAtomic | EGhostI | EGhost

private
let ek_ord (ek : effect_kind_enum) : int
  = match ek with
  | EGhost  -> 0
  | EGhostI -> 1
  | EAtomic -> 2
  | ESteel  -> 3

private
let ek_le (ek0 ek1 : effect_kind_enum) : bool
  = ek_ord ek0 <= ek_ord ek1

let collect_effect_kind (t : term) : Tac (option effect_kind_enum)
  =
    if Tv_Uvar? (inspect t) then None
    else begin
      let hd = collect_fvar (collect_app t)._1 in
      Some (if hd = (`%SH.KSteel ) then ESteel
       else if hd = (`%SH.KAtomic) then EAtomic
       else if hd = (`%SH.KGhostI) then EGhostI
       else if hd = (`%SH.KGhost ) then EGhost
       else fail "collect_effect_kind")
    end

let combinable_bind_steel (a0 a1 : Type u#a)
  : combinable_bind_repr a0 a1 SH.KSteel SH.KSteel SH.KSteel
  by (norm [delta_attr [`%__repr_M__]])
  = fun f g -> C.bind f g

let combinable_bind_ghostI (a0 a1 : Type u#a) (opened : Mem.inames)
  : combinable_bind_repr a0 a1 (SH.KGhostI opened) (SH.KGhostI opened) (SH.KGhostI opened)
  by (norm [delta_attr [`%__repr_M__]])
  = fun f g -> C.bind_ek (SH.KGhostI opened) (SH.KGhostI opened) (SH.KGhostI opened)
      (fun a b f g pre itm post cf cg rf rg -> C.bind_ghostI_steel a b opened f g pre itm post cf cg rf rg)
      f g

let combinable_bind_atomicL (a0 a1 : Type u#a) (opened : Mem.inames)
  : combinable_bind_repr a0 a1 (SH.KAtomic opened) (SH.KGhostI opened) (SH.KAtomic opened)
  by (norm [delta_attr [`%__repr_M__]])
  = fun f g -> C.bind_ek (SH.KAtomic opened) (SH.KGhostI opened) (SH.KAtomic opened)
      (fun a b f g pre itm post cf cg rf rg -> C.bind_atomic_ghost_steel a b opened f g pre itm post cf cg rf rg)
      f g

let combinable_bind_atomicR (a0 a1 : Type u#a) (opened : Mem.inames)
  : combinable_bind_repr a0 a1 (SH.KGhostI opened) (SH.KAtomic opened) (SH.KAtomic opened)
  by (norm [delta_attr [`%__repr_M__]])
  = fun f g -> C.bind_ek (SH.KGhostI opened) (SH.KAtomic opened) (SH.KAtomic opened)
      (fun a b f g pre itm post cf cg rf rg -> C.bind_ghost_atomic_steel a b opened f g pre itm post cf cg rf rg)
      f g

let combinable_bind_ghost (a0 a1 : Type u#a) (opened : Mem.inames)
  : combinable_bind_repr a0 a1 (SH.KGhost opened) (SH.KGhost opened) (SH.KGhost opened)
  by (norm [delta_attr [`%__repr_M__]])
  = fun f g -> C.bind_ghost f g

let combinable_bind_op (ek0 ek1 : effect_kind_enum) : term
  = match if ek0 `ek_le` ek1 then ek1 else ek0 with
  | EGhost  -> (`combinable_bind_ghost)
  | EGhostI -> (`combinable_bind_ghostI)
  | EAtomic -> let ek' = if ek0 `ek_le` ek1 then ek1 else ek0 in
              if ek' `ek_le` EGhostI
              then (if ek0 = EAtomic then (`combinable_bind_atomicL) else (`combinable_bind_atomicR))
              else (`combinable_bind_steel)
  | ESteel  -> (`combinable_bind_steel)


private
let __build_combinable_ite_t
      (ek2 : SH.effect_kind{~ (SH.KAtomic? ek2)}) (a : Type) (ek0 ek1 : SH.effect_kind)
      (lt0 : C.steel_liftable a ek0 ek2) (lt1 : C.steel_liftable a ek1 ek2)
  = Mkcombinable_ite_t #a #ek0 #ek1 #ek2 () lt0 lt1

let combinable_ite_ghost  o = __build_combinable_ite_t (SH.KGhost  o)
let combinable_ite_ghostI o = __build_combinable_ite_t (SH.KGhostI o)
let combinable_ite_steel    = __build_combinable_ite_t  SH.KSteel

let combinable_ite_op (ek0 ek1 : effect_kind_enum) : term
  = match if ek0 `ek_le` ek1 then ek1 else ek0 with
  | EGhost  -> (`combinable_ite_ghost)
  | EGhostI -> (`combinable_ite_ghostI)
  | EAtomic | ESteel -> (`combinable_ite_steel)


/// Try to solves a goal [combinable_bind_t a0 a1 ek0 ek1 ek2] or [combinable_ite_t a ek0 ek1 ek2]:
/// - succeed and returns true if the heads of ek0 and ek1 are known.
/// - otherwise, returns false.
let build_combinable () : Tac bool
  =
    let hd, args = collect_app (cur_goal ()) in
    let hd = try collect_fvar hd with _ -> "unexpected shape" in
    if hd = (`%combinable_bind_t)
    then begin
      guard (L.length args = 5);
      let ek0 = collect_effect_kind (L.index args 2)._1 in
      let ek1 = collect_effect_kind (L.index args 3)._1 in
      match ek0, ek1 with
      | Some ek0, Some ek1 ->
             let op = combinable_bind_op ek0 ek1 in
             apply (`Mkcombinable_bind_t);
             // cba_bind_repr
             apply op;
             // cba_bind_lift0
             build_steel_liftable ();
             // cba_bind_lift1
             build_steel_liftable ();
             true
      | _ -> false
    end else if hd = (`%combinable_ite_t)
    then begin
      guard (L.length args = 4);
      let ek0 = collect_effect_kind (L.index args 1)._1 in
      let ek1 = collect_effect_kind (L.index args 2)._1 in
      match ek0, ek1 with
      | Some ek0, Some ek1 ->
             let op = combinable_ite_op ek0 ek1 in
             apply op;
             // cba_ite_lift0
             build_steel_liftable ();
             // cba_ite_lift1
             build_steel_liftable ();
             true
      | _ -> false
    end else fail "build_combinable : goal_shape"

let rec solve_combinables_round () : Tac (bool & list goal)
  = match goals () with
    | [] -> false, []
    | g :: _ ->
        if build_combinable ()
        then
          let _, gs = solve_combinables_round () in
          true, gs
        else begin
          dismiss ();
          let b, gs = solve_combinables_round () in
          b, g :: gs
        end

let rec solve_combinables () : Tac unit
  = match goals () with
  | [] -> ()
  | _ :: _ ->
    let b, gs = solve_combinables_round () in
    if not b then fail "solve_combinables: could not progress";
    set_goals gs;
    solve_combinables ()

private
let __build_mrepr_to_steel_norew
      (flags : list flag)
      (a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      (t : prog_tree a)
      (goal : (impl : ((pre : M.pre_t) -> (post : M.post_t a) -> (c : M.tree_cond t pre post) ->
                          M.repr_steel_t SH.KSteel a pre post (M.tree_req t c) (M.tree_ens t c))) ->
              ES.__to_steel_goal a pre post req ens M.({repr_tree = t; repr_steel = impl}))
  : mrepr_to_steel_t flags a SH.KSteel pre post req ens t
  = MReprToSteel (fun r -> SH.steel_f (goal r.repr_steel))

/// Solves a goal [mrepr_to_steel_t flags a ek pre post req ens t] using [ES.build_to_steel].
let build_mrepr_to_steel_norew (fr : flags_record) : Tac unit
  =
    apply (`__build_mrepr_to_steel_norew);
    let impl = intro () in
    //exact (`((_ by (ES.build_to_steel (make_flags_record (`#flags)))) <: (`#(cur_goal ()))))
    ES.build_to_steel fr


inline_for_extraction noextract
let steel_of_repr_ek
      (#ek : SH.effect_kind {SH.KSteel? ek \/ SH.KGhost? ek}) // TODO derive for the other effects
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : M.to_repr_t a pre post req ens)
      (f : M.repr_steel_t ek a tr.r_pre tr.r_post tr.r_req tr.r_ens)
  : SH.steel a pre post req ens ek
  = match ek with
  | SH.KSteel   -> SH.steel_f (M.steel_of_repr tr f)
  | SH.KGhost o -> SH.ghost_f (M.steel_ghost_of_repr #a #o tr f)

private
let __build_mrepr_to_steel_wrew
      (flags : list flag)
      (ek : SH.effect_kind)
      (a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      (t : prog_tree a)
      (ek_restr : squash (SH.KSteel? ek \/ SH.KGhost? ek))
      (goal_tr : M.to_repr_t a pre post req ens)
      (goal_sp : ES.to_steel_goal_spec a goal_tr.r_pre goal_tr.r_post goal_tr.r_req goal_tr.r_ens t)
  : mrepr_to_steel_t flags a ek pre post req ens t
  = MReprToSteel (fun r ->
      steel_of_repr_ek goal_tr
        (let lc1 = LV.lc_sub_push goal_sp.goal_spec_LV in
         ES.prog_LV_to_Fun_extract_wp r goal_sp.goal_spec_LV lc1 ()
            goal_tr.r_req goal_tr.r_ens (fun sl0 -> goal_sp.goal_spec_WP)))

/// Solves a goal [mrepr_to_steel_t flags a ek pre post req ens t] using a [rewrite_with_tactic] to avoid
/// normalizing the WP twice.
let build_mrepr_to_steel_wrew (fr : flags_record) (flags : list flag) : Tac unit
  =
    let fr    = make_flags_record flags in
    apply_raw (`__build_mrepr_to_steel_wrew);

    // ek_restr
    norm [delta; iota; simplify];
    trivial ();

    // goal_tr
    let t = timer_start "specs     " fr.f_timer in
    TcS.build_to_repr_t fr (fun () -> [Info_location "in the specification"]);

    // goal_sp
    norm [delta_attr [`%__tac_helper__]; iota];
    let t = ES.build_to_steel_wrew fr flags t in

    timer_stop t


/// On a goal [mrepr_to_steel_t flags a ek pre post req ens t] returns [flags].
let collect_flags () : Tac (list flag)
  =
    let args = (collect_app (cur_goal ()))._2      in
    guard (L.length args = 8);
    unquote (L.hd args)._1

/// Solves a goal [mrepr_to_steel_t flags a ek pre post req ens t].
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

    //let t = timer_start "implicits" true in

    iterAll (fun () -> intros' (); try trefl () with _ -> ());
    let fgoals = mrepr_implicits_init (Mkfilter_goals_r [] [] []) in

    // Solve the combinable_* goals
    set_goals fgoals.fgoals_comb;
    solve_combinables ();

    // Solve the [steel_liftable] from the lifting to ConvEffect
    set_goals fgoals.fgoals_lift;
    iterAll build_steel_liftable;

    //timer_stop t;

    
    // useful to debug `Tactic left uninstantiated unification variable` errors
    //dump_all true "implicits";

    // Solve the [mrepr_to_steel_t] goal
    set_goals fgoals.fgoals_tstl;
    iterAll build_mrepr_to_steel
  )


(*** Notations *)

unfold
let usteel = SH.unit_steel

unfold
let usteel_ghost = SH.unit_steel_ghost


let to_steel
      (#[apply (`[])] flags : list flag)
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (r : unit -> ConvEffect a SH.KSteel pre post req ens flags)
  : usteel a pre post req ens
  = SH.steel_u (reify (r ()))

let to_steel_g
      (#[apply (`[])] flags : list flag)
      (#a : Type) (#opened : Mem.inames)
      (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (r : unit -> ConvEffect a (SH.KGhost opened) pre post req ens flags)
  : usteel_ghost a opened pre post req ens
  = SH.ghost_u (reify (r ()))
