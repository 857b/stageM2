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

type repr_eq (a : Type) (ek : SH.effect_kind) (t : M.prog_tree u#a u#p a) : Type
  = r : M.repr u#a u#p ek a { r.repr_tree == t }

type repr' = repr_eq u#a u#8

/// We want to avoid a retypechecking of the [M.prog_tree] which may fail because of
/// the monotonicity refinement on [pure_wp].
/// For this reason, we convert our representation to Steel directly in the effect using a
/// [repr_cv] field, which contains the conversion if the [cvi] index is set to some
/// specification.

noeq
type conv_index (a : Type u#a) = {
  cvi_pre   : SE.pre_t;
  cvi_post  : SE.post_t a;
  cvi_req   : SE.req_t cvi_pre;
  cvi_ens   : SE.ens_t cvi_pre a cvi_post;
  cvi_flags : list flag;
}

noeq
type indexed_option (a : Type) (f : a -> Type) : option a -> Type =
  | ISome : (x : a) -> (v : f x) -> indexed_option a f (Some x)
  | INone : indexed_option a f None


// location placeholder
type location_p = | LocationP

type location_goal (sub : list location_p) = location_p

let locm (l : location_p) : location_p = l


noeq
type repr (a : Type) (ek : SH.effect_kind) (t : prog_tree a)
          (cvi : option (conv_index a)) (loc : location_p) =
  {
    repr_M  : repr' a ek t;
    repr_cv : indexed_option
                (conv_index a) (fun c -> SH.steel a c.cvi_pre c.cvi_post c.cvi_req c.cvi_ens ek)
                cvi
  }

let mk_repr (#a : Type) (#ek : SH.effect_kind) (#t : prog_tree a) (repr_M : repr' a ek t)
  : repr a ek t None LocationP
  = {
    repr_M;
    repr_cv = INone
  }

(***** return *)

let return_ghostI
      (a : Type) (x : a) (#[@@@ __mrepr_implicit__] opened: Mem.inames)
      (#[@@@ __mrepr_implicit__] loc : location_goal [])
  : repr u#a a (SH.KGhostI opened) (M.Tret a x (fun _ -> [])) None (locm loc)
  = mk_repr (C.return (SH.KGhostI opened) #a x)


(***** bind *)

[@@ __repr_M__]
noeq inline_for_extraction
type combine_bind_t
       (a : Type u#a) (b : Type u#b)
       (ek0 ek1 ek : SH.effect_kind)
       (f : prog_tree a) (g : a -> prog_tree b)
= {
  cb_bind_repr : prog_tree b;
  cb_bind_impl : (rf : repr' a ek0 f) -> (rg : ((x : a) -> repr' b ek1 (g x))) ->
                 repr' b ek cb_bind_repr
}

type combinable_bind_repr (a0 a1 : Type u#a) (ek0 ek1 ek2 : SH.effect_kind)
  = (f : M.repr u#a u#8 ek0 a0) -> (g : ((x : a0) -> M.repr u#a u#8 ek1 a1)) ->
    repr_eq a1 ek2 (M.Tbind a0 a1 f.repr_tree (fun x -> (g x).repr_tree))

let repr_tree_eq #a #ek #t (r : repr_eq a ek t) : squash (r.repr_tree == t)
  = ()

noeq inline_for_extraction
type combinable_bind_t (a0 a1 : Type u#a) (ek0 ek1 ek2 : SH.effect_kind) = {
  cba_bind_ek0'  : SH.effect_kind;
  cba_bind_ek1'  : SH.effect_kind;
  // Sometime ek2 has already been resolved (for instance in test9', maybe because the effect_kind
  // are not marked as [__repr_implicit__])
  cba_bind_ek2'  : SH.effect_kind;
  cba_bind_repr  : combinable_bind_repr a0 a1 cba_bind_ek0' cba_bind_ek1' cba_bind_ek2';
  cba_bind_lift0 : C.steel_liftable a0 ek0 cba_bind_ek0';
  cba_bind_lift1 : C.steel_liftable a1 ek1 cba_bind_ek1';
  cba_bind_lift2 : C.steel_liftable a1 cba_bind_ek2' ek2;
}

[@@ __repr_M__]
inline_for_extraction
let combine_bind
      (a : Type u#b) (b : Type u#b)
      (ek0 ek1 ek2 : SH.effect_kind)
      (cba : combinable_bind_t a b ek0 ek1 ek2)
      (f : prog_tree a) (g : a -> prog_tree b)
  : combine_bind_t a b ek0 ek1 ek2 f g
  =
    let t = M.Tbind a b f (fun x -> g x) in // We need the functional extensionality so we eta-expend g
  {
    cb_bind_repr = t;
    cb_bind_impl = (fun rf rg ->
                      let rf' = C.repr_lift cba.cba_bind_lift0 rf                        in
                      let rg' (x : a) = C.repr_lift cba.cba_bind_lift1 (rg x)            in
                      let r = C.repr_lift cba.cba_bind_lift2 (cba.cba_bind_repr rf' rg') in
                      U.funext_eta (fun x -> g x) (fun x -> (rg' x).repr_tree)
                        (U.by_refl ()) (U.by_refl ())
                        (fun x -> ());
                      calc (==) {
                        r.repr_tree;
                      == { }
                        (cba.cba_bind_repr rf' rg').repr_tree;
                      == { _ by T.(apply (`repr_tree_eq)) }
                        M.Tbind a b rf'.repr_tree (fun x -> (rg' x).repr_tree);
                      == { }
                        t;
                      };
                      r);
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
      (loc_f loc_g : location_p)
      (#[@@@ __mrepr_implicit__] loc : location_goal [loc_f; loc_g])
      (rf : repr u#a a ek0 f None loc_f) (rg : (x : a) -> repr u#b b ek1 (g x) None loc_g)
  : repr u#b b ek (cb f g).cb_bind_repr None (locm loc)
  = mk_repr ((cb f g).cb_bind_impl rf.repr_M (fun x -> (rg x).repr_M))


(***** subcomp *)

noeq
type combine_subcomp_t
      (a : Type u#a) (ek0 ek1 : SH.effect_kind) (f : prog_tree a) (g : prog_tree a)
      (cvi : option (conv_index a)) (loc : location_p)
  = {
    cba_subc : repr a ek0 f None LocationP -> repr a ek1 g cvi LocationP;
  }

noeq
type mrepr_to_steel_t
       (flags : list flag)
       (a : Type) (ek : SH.effect_kind)
       (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
       (t : prog_tree a)
  = | MReprToSteel of (repr' a ek t -> SH.steel a pre post req ens ek)

private
type dummy_spec (a : Type u#a) (sp : M.spec_r a) : Type u#b =

private
let dummy_prog_tree (a : Type u#a) : prog_tree a
  = M.Tspec a (dummy_spec a)

private
let dummy_repr (a : Type u#a) (ek : SH.effect_kind) : repr' a ek (dummy_prog_tree a)
  = {
    repr_tree  = dummy_prog_tree a;
    repr_steel = (fun pre post c -> false_elim ())
  }

/// This subcomp is used at top-level, to convert our representation to Steel. To avoid the retypechecking of
/// [t], we replace it with [dummy_prog_tree].
let combine_subcomp_convert
      (#loc : location_p)
      (a : Type u#a) (ek0 ek1 : SH.effect_kind) (t : prog_tree a)
      (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post) (flags : list flag)
      (lt : C.steel_liftable a ek0 ek1)
      (cv : mrepr_to_steel_t flags a ek1 pre post req ens t)
  : combine_subcomp_t a ek0 ek1 t (dummy_prog_tree a) (Some (Mkconv_index pre post req ens flags)) loc
  = Mkcombine_subcomp_t (fun r ->
      let r' = C.repr_lift lt r.repr_M in
      let MReprToSteel cv = cv in
      {
        repr_M = dummy_repr a ek1;
        repr_cv = ISome _ (cv r')
      })

let subcomp
      (a : Type u#a)
      (#ek0 : SH.effect_kind) (#ek1 : SH.effect_kind)
      (#f : prog_tree a) (#g : prog_tree a)
      (cvi : option (conv_index a))
      (#loc_f : location_p) (#[@@@ __mrepr_implicit__] loc_g : location_goal [])
      (#[@@@ __mrepr_implicit__] cb : combine_subcomp_t a ek0 ek1 f g cvi loc_f)
      (rf : repr a ek0 f None loc_f)
  : repr a ek1 g cvi (locm loc_g)
  = cb.cba_subc rf


(***** if then else *)

// We match the restriction of SteelAtomic, but we do not need it
type cba_ite_effect_kind_t =
  ek : SH.effect_kind { ~ (SH.KAtomic? ek) }

noeq
type combinable_ite_t (a : Type) (ek0 ek1 ek2 : SH.effect_kind) = {
  cba_ite_ek2'  : cba_ite_effect_kind_t;
  cba_ite_lift0 : C.steel_liftable a ek0 cba_ite_ek2';
  cba_ite_lift1 : C.steel_liftable a ek1 cba_ite_ek2';
  cba_ite_lift2 : C.steel_liftable a cba_ite_ek2' ek2;
}

let if_then_else
      (a : Type)
      (#ek0 #ek1 #ek2 : SH.effect_kind)
      (#thn : prog_tree a) (#els : prog_tree a)
      (#[@@@ __mrepr_implicit__] cb : combinable_ite_t a ek0 ek1 ek2)
      (#loc_f #loc_g : location_p)
      (#[@@@ __mrepr_implicit__] loc : location_goal [loc_f; loc_g])
      (rthn : repr a ek0 thn None loc_f) (rels : repr a ek1 els None loc_g)
      (guard : bool)
  : Type
  = repr a ek2 (M.Tif a guard thn els) None (locm loc)


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
      (#loc : location_p) (a : Type) (ek0 ek1 ek2 : SH.effect_kind) (guard : bool) (thn els : prog_tree a)
      (_ : squash guard)
      (l0 : C.steel_liftable a ek0 ek1) (l1 : C.steel_liftable a ek1 ek2)
  : combine_subcomp_t a ek0 ek2 thn (M.Tif a guard thn els) None loc
  = Mkcombine_subcomp_t (fun rthn -> mk_repr ({
    repr_tree  = M.Tif a guard thn els;
    repr_steel = (fun pre0 post0 c ->
                    let M.TCif pre post cthn cels = c in
                    ite_steel_thn a ek2 guard thn els pre post cthn cels
                         ((C.repr_lift l1 (C.repr_lift l0 rthn.repr_M)).repr_steel _ _  cthn) ())
  }))

let ite_combine_els
      (#loc : location_p) (a : Type) (ek0 ek1 ek2 : SH.effect_kind) (guard : bool) (thn els : prog_tree a)
      (_ : squash (~guard))
      (l0 : C.steel_liftable a ek0 ek1) (l1 : C.steel_liftable a ek1 ek2)
  : combine_subcomp_t a ek0 ek2 els (M.Tif a guard thn els) None loc
  = Mkcombine_subcomp_t (fun rels -> mk_repr ({
    repr_tree  = M.Tif a guard thn els;
    repr_steel = (fun pre0 post0 c ->
                    let M.TCif pre post cthn cels = c in
                    ite_steel_els a ek2 guard thn els pre post cthn cels
                          ((C.repr_lift l1 (C.repr_lift l0 rels.repr_M)).repr_steel _ _ cels) ())
  }))


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
    ];
    apply (`Mkcombinable_ite_t?.cba_ite_lift2)
  )


[@@ ite_soundness_by __ite_soundness__; allow_informative_binders]
total reflectable reifiable effect {
  MRepr (a : Type) (ek : SH.effect_kind) (t : prog_tree a)
        (cvi : option (conv_index a)) (loc : location_p)
  with {
    repr;
    return = return_ghostI;
    bind   = bind_;
    subcomp;
    if_then_else;
  }
}

let return (#a : Type u#a) (#opened : Mem.inames) (#[@@@ __mrepr_implicit__] loc : location_goal []) (x : a)
  : MRepr a (SH.KGhostI opened) (M.Tret a x (fun _ -> [])) None (locm loc)
  = MRepr?.reflect (return_ghostI a x #opened)

let return_hint (#a : Type u#a) (#opened : Mem.inames) (#[@@@ __mrepr_implicit__] loc : location_goal []) (x : a)
                (sl_hint : M.post_t a)
  : MRepr a (SH.KGhostI opened) (M.Tret a x sl_hint) None (locm loc)
  = MRepr?.reflect (mk_repr (C.return_hint (SH.KGhostI opened) #a x sl_hint))


(***** bind (PURE, MRepr) |> MRepr *)

[@@ __repr_M__]
noeq inline_for_extraction
type combine_bind_pure_t
       (a : Type u#r) (b : Type u#a)
       (ek : SH.effect_kind)
       (wp : pure_wp a) (g : a -> M.prog_tree u#a u#p b)
= {
  cb_bindP_repr : M.prog_tree u#a u#p b;
  cb_bindP_impl : (rf : unit -> PURE a wp) -> (rg : ((x : a) -> repr_eq b ek (g x))) ->
                  repr_eq u#a u#p b ek cb_bindP_repr
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
                       let r = C.bindP #(UV.raise_t u#r u#8 a) #b ek (UV.raise_pure_wp u#r u#8 wp)
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
      (#ek : SH.effect_kind)
      (#wp : pure_wp a)
      (#g : a -> prog_tree b)
      (#[@@@ __mrepr_implicit__] cb
        : (wp : pure_wp a) -> (g : (a -> prog_tree b)) -> combine_bind_pure_t u#r u#a u#8 a b ek wp g)
      (#loc_g : location_p)
      (#[@@@ __mrepr_implicit__] loc : location_goal [loc_g])
      (rf : eqtype_as_type unit -> PURE a wp)
      (rg : (x : a) -> repr b ek (g x) None loc_g)
  : repr b ek (cb wp g).cb_bindP_repr None (locm loc)
  = mk_repr ((cb wp g).cb_bindP_impl rf (fun x -> (rg x).repr_M))

#push-options "--warn_error -330"
polymonadic_bind (PURE, MRepr) |> MRepr = bind_pure_mrepr
#pop-options


(**** MReprGhost effect *)

/// In order to be able to use ghost operation in SteelGhost operations, we declare a MReprGhost effect, with the
/// same representation as MRepr, but with the effect_kind fixed to [KGhost] and declared as erasable.
/// We do not use new_effect in order to change the effect_kind of the return combinator.
// ALT: fix the combinator (bind, if then else) in the effect instead of relying on tactics to always infer
//      the ghost combinator

type repr_ghost (a : Type u#a) (opened : Mem.inames) (t : prog_tree a)
                (cvi : option (conv_index a)) (loc : location_p) =
  repr a (SH.KGhost opened) t cvi loc

let return_ghost
      (a : Type) (x : a) (#opened: Mem.inames)
      (#[@@@ __mrepr_implicit__] loc : location_goal [])
  : repr_ghost u#a a opened (M.Tret a x (fun _ -> [])) None (locm loc)
  = mk_repr (C.return (SH.KGhost opened) #a x)

let bind_ghost
      (a : Type u#a) (b : Type u#b)
      (#o : Mem.inames)
      (#f : prog_tree a) (#g : a -> prog_tree b)
      (#[@@@ __mrepr_implicit__] cb
        : (f : prog_tree a) -> (g : (a -> prog_tree b)) ->
          combine_bind_t a b (SH.KGhost o) (SH.KGhost o) (SH.KGhost o) f g)
      (loc_f loc_g : location_p)
      (#[@@@ __mrepr_implicit__] loc : location_goal [loc_f; loc_g])
      (rf : repr_ghost u#a a o f None loc_f) (rg : (x : a) -> repr_ghost u#b b o (g x) None loc_g)
  : repr_ghost u#b b o (cb f g).cb_bind_repr None (locm loc)
  = mk_repr ((cb f g).cb_bind_impl rf.repr_M (fun x -> (rg x).repr_M))

let subcomp_ghost
      (a : Type u#a)
      (#o : Mem.inames)
      (#f : prog_tree a) (#g : prog_tree a)
      (cvi : option (conv_index a))
      (#loc_f : location_p) (#[@@@ __mrepr_implicit__] loc_g : location_goal [])
      (#[@@@ __mrepr_implicit__] cb : combine_subcomp_t a (SH.KGhost o) (SH.KGhost o) f g cvi loc_f)
      (rf : repr_ghost a o f None loc_f)
  : repr_ghost a o g cvi (locm loc_g)
  = cb.cba_subc rf

let if_then_else_ghost
      (a : Type)
      (#o : Mem.inames)
      (#thn : prog_tree a) (#els : prog_tree a)
      (#[@@@ __mrepr_implicit__] cb : combinable_ite_t a (SH.KGhost o) (SH.KGhost o) (SH.KGhost o))
      (#loc_f #loc_g : location_p)
      (#[@@@ __mrepr_implicit__] loc : location_goal [loc_f; loc_g])
      (rthn : repr_ghost a o thn None loc_f) (rels : repr_ghost a o els None loc_g)
      (guard : bool)
  : Type
  = repr_ghost a o (M.Tif a guard thn els) None (locm loc)


[@@ erasable; ite_soundness_by __ite_soundness__; allow_informative_binders]
total reflectable reifiable effect {
  MReprGhost (a : Type) (opened : Mem.inames) (t : prog_tree a)
             (cvi : option (conv_index a)) (loc : location_p)
  with {
    repr         = repr_ghost;
    return       = return_ghost;
    bind         = bind_ghost;
    subcomp      = subcomp_ghost;
    if_then_else = if_then_else_ghost;
  }
}

let return_g (#a : Type u#a) (#opened : Mem.inames) (#[@@@ __mrepr_implicit__] loc : location_goal []) (x : a)
  : MReprGhost a opened (M.Tret a x (fun _ -> [])) None (locm loc)
  = MReprGhost?.reflect (return_ghost a x #opened)

let return_g_hint (#a : Type u#a) (#opened : Mem.inames) (#[@@@ __mrepr_implicit__] loc : location_goal []) (x : a)
                  (sl_hint : M.post_t a)
  : MReprGhost a opened (M.Tret a x sl_hint) None (locm loc)
  = MReprGhost?.reflect (mk_repr (C.return_hint (SH.KGhost opened) #a x sl_hint))


let bind_pure_mrepr_ghost
      (a : Type u#r) (b : Type u#a)
      (#o : Mem.inames)
      (#wp : pure_wp a)
      (#g : a -> prog_tree b)
      (#[@@@ __mrepr_implicit__] cb
        : (wp : pure_wp a) -> (g : (a -> prog_tree b)) -> combine_bind_pure_t u#r u#a u#8 a b (SH.KGhost o) wp g)
      (#loc_g : location_p)
      (#[@@@ __mrepr_implicit__] loc : location_goal [loc_g])
      (rf : eqtype_as_type unit -> PURE a wp)
      (rg : (x : a) -> repr_ghost b o (g x) None loc_g)
  : repr_ghost b o (cb wp g).cb_bindP_repr None (locm loc)
  = mk_repr ((cb wp g).cb_bindP_impl rf (fun x -> (rg x).repr_M))

#push-options "--warn_error -330"
polymonadic_bind (PURE, MReprGhost) |> MReprGhost = bind_pure_mrepr_ghost
#pop-options

/// The [steel_liftable] condition is equivalent to [C.erasable_t a].
/// If [a] is not erasable F* should raise an error when using this lift but since [repr_ghost] is a
/// SteelGhost and [repr _ (SH.KGhostI) _] is a SteelAGcommon, we still need to do our own lift.
let lift_mrepr_ghost_mrepr
      (a : Type) (opened: Mem.inames)
      (#t : prog_tree a)
      (#[@@@ __mrepr_implicit__] lt : C.steel_liftable a (SH.KGhost opened) (SH.KGhostI opened))
      (#loc : location_p)
      (r : repr_ghost a opened t None loc)
  : repr a (SH.KGhostI opened) t None loc
  = mk_repr (C.repr_lift lt r.repr_M)

sub_effect MReprGhost ~> MRepr = lift_mrepr_ghost_mrepr


(**** lifting Steel ~> MRepr *)

/// The sub_effect is not working (order of resolution of the implicits, use of Steel's combinators instead of
/// MRepr's combinators, Steel computation unexpectedly lifted where MRepr does not appear).
/// One has to use an explicit cast ([call]) instead.

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
      (#[@@@ __mrepr_implicit__] loc : location_goal [])
      ($f : (x : b) -> SE.Steel (a x) (pre x) (post x) (req x) (ens x)) (x : b)
  : MRepr (a x) SH.KSteel
      (M.Tspec (a x) (M.spec_r_steel u#a u#8 (pre x) (post x) (req x) (ens x)))
      None (locm loc)
  = MRepr?.reflect
      (mk_repr (C.repr_of_steel #(a x) (pre x) (post x) (req x) (ens x) (SH.steel_fe (fun () -> f x))))

unfold
let call_a (#b : Type u#b)
      (#a : b -> Type) (#opened : b -> Mem.inames) (#pre : b -> SE.pre_t) (#post : (x : b) -> SE.post_t (a x))
      (#req : (x : b) -> SE.req_t (pre x)) (#ens : (x : b) -> SE.ens_t (pre x) (a x) (post x))
      (#[@@@ __mrepr_implicit__] loc : location_goal [])
      ($f : (x : b) -> SA.SteelAtomic (a x) (opened x) (pre x) (post x) (req x) (ens x)) (x : b)
  : MRepr (a x) (SH.KAtomic (opened x))
      (M.Tspec (a x) (M.spec_r_steel u#a u#8 (pre x) (post x) (req x) (ens x)))
      None (locm loc)
  = MRepr?.reflect (mk_repr
      (C.repr_of_steel #(a x) (pre x) (post x) (req x) (ens x) (SH.atomic_fe (fun () -> f x))))

unfold
let call_g (#b : Type u#b)
      (#a : b -> Type) (#opened : b -> Mem.inames) (#pre : b -> SE.pre_t) (#post : (x : b) -> SE.post_t (a x))
      (#req : (x : b) -> SE.req_t (pre x)) (#ens : (x : b) -> SE.ens_t (pre x) (a x) (post x))
      (#[@@@ __mrepr_implicit__] loc : location_goal [])
      ($f : (x : b) -> SA.SteelGhost (a x) (opened x) (pre x) (post x) (req x) (ens x)) (x : b)
  : MReprGhost (a x) (opened x)
      (M.Tspec (a x) (M.spec_r_steel u#a u#8 (pre x) (post x) (req x) (ens x)))
      None (locm loc)
  = MReprGhost?.reflect (mk_repr
       (C.repr_of_steel #(a x) (pre x) (post x) (req x) (ens x) (SH.ghost_fe (fun () -> f x))))


(*** Resolution of [__mrepr_implicit__] *)

module ES = Experiment.Steel
module LV = Experiment.Steel.Repr.LV

open FStar.Tactics
open Learn.Tactics.Util
open Experiment.Steel.Tac

(***** stage 1 *)

private noeq
type filter_goals_r = {
  // combinable_bind_t, combinable_ite_t
  fgoals_comb : list goal;
  // steel_liftable
  fgoals_lift : list goal;
  // combine_subcomp_t
  fgoals_subc : list goal;
  // location goals
  fgoals_loca : list goal;
}

let already_solved (g : goal) : Tac bool
  = Tv_Uvar? (inspect (goal_witness g))

let rec mrepr_implicits_init (fr : flags_record) (gs : list goal) (r : filter_goals_r) : Tac filter_goals_r
  =
    match gs with
    | [] -> r
    | g :: gs ->
      set_goals [g];
      let r =
        if not (already_solved g)
        then r // the goal has already been solved
        else begin
          let app = collect_app (goal_type g) in
          let hd  = cs_try (fun () -> collect_fvar app._1)
                      fr dummy_ctx (fun m -> fail (m (Fail_goal_shape (GShape_repr_implicit)) []))
          in
          // The only sources of failure here should be a bind where the two types involved belong to
          // different universes. Or a polymonadic bind with an universe greater than [u#8].
          if hd = (`%combine_bind_t)
          then begin
              apply (`combine_bind);
              // combinable_bind_t
              let g = _cur_goal () in
              {r with fgoals_comb = g :: r.fgoals_comb}
          end else if hd = (`%combine_bind_pure_t)
          then (apply (`combine_bind_pure); r)

          else if hd = (`%combinable_ite_t)
          then {r with fgoals_comb = g :: r.fgoals_comb}
          else if hd = (`%C.steel_liftable)
          then {r with fgoals_lift = g :: r.fgoals_lift}
          else if hd = (`%combine_subcomp_t)
          then {r with fgoals_subc = g :: r.fgoals_subc}
          else if hd = (`%location_goal)
          then (dismiss (); {r with fgoals_loca = g :: r.fgoals_loca})
          else if hd = (`%Mem.inames)
          then r // should be inferred as side effects of other goals
          else cs_raise fr dummy_ctx (fun m -> fail (m (Fail_goal_shape (GShape_repr_implicit)) []))
        end
      in
      mrepr_implicits_init fr gs r

(***** stage 2 *)

/// Solves a goal [C.steel_liftable a ek0 ek1].
/// Since we start by trying to apply [C.Rt1n_refl], if [ek0] or [ek1] is an uvar, we will choose a trivial lift.
let rec build_steel_liftable_aux fr ctx : Tac unit
  =
    try apply (`C.Rt1n_refl)
    with _ ->
      apply (`C.Rt1n_trans);
      // lift1
      begin
        match catch (fun () -> apply (`C.Lift_ghost_ghostI)) with
        | Inr () -> C.build_erasable_t fr ctx
        | Inl _ ->
        try apply (`C.Lift_ghostI_atomic) with _ ->
        try apply (`C.Lift_atomic_steel)  with _ ->
        cs_raise fr ctx (fun m -> fail (m Fail_liftable []))
      end;

      build_steel_liftable_aux fr ctx

let build_steel_liftable fr ctx : Tac unit
  =
    let goal = cur_goal () in
    build_steel_liftable_aux fr (ctx_app_info ctx [Info_goal goal])


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

let collect_effect_kind fr ctx (t : term) : Tac (option effect_kind_enum)
  =
    if Tv_Uvar? (inspect t) then None
    else begin
      let hd = cs_try (fun () -> collect_fvar (collect_app t)._1)
                 fr ctx (fun m -> fail (m (Fail_goal_shape GShape_effect_kind) [])) in
      Some (if hd = (`%SH.KSteel ) then ESteel
       else if hd = (`%SH.KAtomic) then EAtomic
       else if hd = (`%SH.KGhostI) then EGhostI
       else if hd = (`%SH.KGhost ) then EGhost
       else cs_raise fr ctx (fun m -> fail (m (Fail_goal_shape GShape_effect_kind) [])))
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


let combinable_ite_ghost  o : cba_ite_effect_kind_t =  SH.KGhost  o
let combinable_ite_ghostI o : cba_ite_effect_kind_t = (SH.KGhostI o)
let combinable_ite_steel    : cba_ite_effect_kind_t =  SH.KSteel

let combinable_ite_kind (ek0 ek1 : effect_kind_enum) : term
  = match if ek0 `ek_le` ek1 then ek1 else ek0 with
  | EGhost  -> (`combinable_ite_ghost)
  | EGhostI -> (`combinable_ite_ghostI)
  | EAtomic | ESteel -> (`combinable_ite_steel)


/// Try to solves a goal [combinable_bind_t a0 a1 ek0 ek1 ek2] or [combinable_ite_t a ek0 ek1 ek2]:
/// - succeed and returns true if the heads of ek0 and ek1 are known.
/// - otherwise, returns false.
let build_combinable fr ctx : Tac bool
  =
    // there are some beta-redexes + aliases
    norm [delta_only [`%combinable_ite_ghost; `%combinable_ite_ghostI; `%combinable_ite_steel]];
    
    let hd, args = collect_app (cur_goal ()) in
    let hd = try collect_fvar hd with _ -> "unexpected shape" in
    if hd = (`%combinable_bind_t)
    then begin
      guard (L.length args = 5);
      let ek0 = collect_effect_kind fr ctx (L.index args 2)._1 in
      let ek1 = collect_effect_kind fr ctx (L.index args 3)._1 in
      match ek0, ek1 with
      | Some ek0, Some ek1 ->
             let op = combinable_bind_op ek0 ek1 in
             apply (`Mkcombinable_bind_t);
             // cba_bind_repr
             seq (fun () -> apply op) dismiss;
             // cba_bind_lift0
             build_steel_liftable fr ctx;
             // cba_bind_lift1
             build_steel_liftable fr ctx;
             // cba_bind_lift2
             build_steel_liftable fr ctx;
             true
      | _ -> false
    end else if hd = (`%combinable_ite_t)
    then begin
      guard (L.length args = 4);
      let ek0 = collect_effect_kind fr ctx (L.index args 1)._1 in
      let ek1 = collect_effect_kind fr ctx (L.index args 2)._1 in
      match ek0, ek1 with
      | Some ek0, Some ek1 ->
             let ek = combinable_ite_kind ek0 ek1 in
             apply_raw (`Mkcombinable_ite_t);
             // cba_ite_ek2'
             seq (fun () -> apply ek) dismiss;
             // cba_ite_lift0
             build_steel_liftable fr ctx;
             // cba_ite_lift1
             build_steel_liftable fr ctx;
             // cba_ite_lift2
             build_steel_liftable fr ctx;
             true
      | _ -> false
    end else fail "build_combinable : goal_shape"

let rec solve_combinables_round fr : Tac (bool & list goal)
  = match goals () with
    | [] -> false, []
    | g :: _ ->
        if build_combinable fr dummy_ctx
        then
          let _, gs = solve_combinables_round fr in
          true, gs
        else begin
          dismiss ();
          let b, gs = solve_combinables_round fr in
          b, g :: gs
        end

let rec solve_combinables fr : Tac unit
  = match goals () with
  | [] -> ()
  | _ :: _ ->
    let b, gs = solve_combinables_round fr in
    if not b then cs_raise fr dummy_ctx (fun m -> fail (m Fail_solve_combinables []));
    set_goals gs;
    solve_combinables fr

(***** stage 3 *)

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

private
let __build_mrepr_to_steel_wrew
      (flags : list flag)
      (ek : SH.effect_kind)
      (a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      (t : prog_tree a)
      (goal_tr : M.to_repr_t a pre post req ens)
      (goal_sp : ES.to_steel_goal_spec a goal_tr.r_pre goal_tr.r_post goal_tr.r_req goal_tr.r_ens t)
  : mrepr_to_steel_t flags a ek pre post req ens t
  = MReprToSteel (fun r ->
      M.steel_of_repr goal_tr
        (let lc1 = LV.lc_sub_push goal_sp.goal_spec_LV in
         ES.prog_LV_to_Fun_extract_wp r goal_sp.goal_spec_LV lc1 ()
            goal_tr.r_req goal_tr.r_ens (fun sl0 -> goal_sp.goal_spec_WP)))

/// Solves a goal [mrepr_to_steel_t flags a ek pre post req ens t] using a [rewrite_with_tactic] to avoid
/// normalizing the WP twice.
let build_mrepr_to_steel_wrew (fr : flags_record) (ctx : cs_context) (flags : list flag) : Tac unit
  =
    let fr = make_flags_record flags in
    apply_raw (`__build_mrepr_to_steel_wrew);

    // goal_tr
    let t = timer_start "specs     " fr.f_timer in
    build_to_repr_t fr (root_ctx ["in the specification"]);

    // goal_sp
    norm [delta_attr [`%__tac_helper__]; iota];
    let t = ES.build_to_steel_wrew fr ctx flags t in

    timer_stop t

/// Solves a goal [mrepr_to_steel_t flags a ek pre post req ens t].
let build_mrepr_to_steel (flags : list flag) (fr : flags_record) (ctx : cs_context) : Tac unit
  =
    if fr.f_wrew
    then build_mrepr_to_steel_wrew  fr ctx flags
    else build_mrepr_to_steel_norew fr

(****** Locations *)

/// Utilities for following a path in the locations

let rec collect_loc_uvar (t : term) : Tac term =
  match inspect t with
  | Tv_Uvar _ _ -> t
  | Tv_App hd (t, Q_Explicit) ->
      guard (collect_fvar hd = (`%locm));
      collect_loc_uvar t
  | _ -> fail "collect_loc_uvar"

/// Returns the i-th element of a list represented as by a term
let rec term_list_nth (l : term) (i : nat) : Tac term =
  // Cons
  let hd, args = collect_app l in
  guard (L.length args = 3);
  if i = 0
  then (L.index args 1)._1
  else term_list_nth (L.index args 2)._1 (i-1)

let rec follow_loc_path (pth : list nat) : Tac unit =
  match pth with
  | [] -> ()
  | i :: pth ->
    try// If there is an error, we stop at the closest goal
      // location_goal
      let gl = inspect (cur_goal ()) in
      guard (Tv_App? gl);
      let Tv_App _ (sub, _) = gl in
      let uv = collect_loc_uvar (term_list_nth sub i) in
      dismiss ();
      unshelve uv;
      follow_loc_path pth 
      with _ -> ()

let rec revert_all_binders () : Tac nat
  = try revert ();
        (revert_all_binders () + 1 <: nat)
    with _ -> 0

private
let __paste_goal (#src #dst : Type) (_ : squash False) (x0 : src) (x1 : src) : dst
  = false_elim ()

let move_to_location (entry_uvar : term) (pth : list nat) : Tac unit
  =
    // Copy the current goal
    let n_bs = revert_all_binders () in
    let copy_uv = fresh_uvar None in
    exact copy_uv;
    // Move to a goal with a more precise location
    unshelve entry_uvar;
    follow_loc_path pth;
    // Paste the goal
    apply (`__paste_goal);
    dismiss (); // squash False
    exact copy_uv;
    let _ = repeatn n_bs intro in
    ()


/// Solves a goal [combine_subcomp_t a ek0 ek1 (ReprIM t) (ReprIS pre post req ens flag) loc]
let solve_conversion_subcomp flags fr : Tac unit
  =
    let args = (collect_app (cur_goal ()))._2 in
    guard (L.length args = 7);
    let entry_loc_uv = try Some (collect_loc_uvar (L.index args 6)._1) with _ -> None in

    apply (`combine_subcomp_convert);
    // lt
    build_steel_liftable fr (root_ctx ["In the top-level subcomp"]);
    // cv
    let ctx = root_ctx_with_move_to [] (fun pth ->
      match entry_loc_uv with
      | None    -> ()
      | Some uv -> try move_to_location uv (L.rev pth) with _ -> ()) in
    build_mrepr_to_steel flags fr ctx

(***** entry *)

/// Search for a goal [combine_subcomp_t _ _ _ _ _ (Some {flags}) _] and returns [flags].
let rec collect_flags (gs : list goal) : Tac (list flag)
  = match gs with
    | [] -> []
    | g :: gs ->
        try
          let app = collect_app (goal_type g) in
          guard (collect_fvar app._1 = (`%combine_subcomp_t));
          guard (L.length app._2 = 7);
          let arg  = (L.index app._2 5)._1 in // Some #_ _
          let args = (collect_app arg)._2  in
          guard (L.length args = 2);
          let arg  = (L.index args 1)._1   in
          let app  = collect_app arg       in
          guard (collect_fvar app._1 = (`%Mkconv_index));
          guard (L.length app._2 = 6);
          unquote (L.index app._2 5)._1
          with _ -> collect_flags gs

[@@ resolve_implicits; __mrepr_implicit__]
let mrepr_implicits_tac () : Tac unit
  = with_policy Force (fun () ->

    ////// Stage 1 //////

    //let t = timer_start "implicits" true in
    let flags = collect_flags (goals ()) in
    let fr    = make_flags_record flags  in
    //dump "implicits";
    iterAll (fun () -> try trefl () with _ -> ());
    iterAll intros';

    let fgoals = mrepr_implicits_init fr (goals ()) (Mkfilter_goals_r [] [] [] []) in

    ////// Stage 2 //////

    // Solve the combinable_* goals
    set_goals fgoals.fgoals_comb;
    solve_combinables fr;

    // Solve the [steel_liftable] goals (from the subcomps MReprGhost ~> MRepr)
    set_goals fgoals.fgoals_lift;
    iterAll (fun () -> build_steel_liftable fr dummy_ctx);

    //timer_stop t;

    // useful to debug `Tactic left uninstantiated unification variable` errors
    //dump_all true "implicits";

    ////// Stage 3 //////

    // Solve the [combine_subcomp_t] goals by building the conversion to Steel ([mrepr_to_steel_t])
    set_goals fgoals.fgoals_subc;
    iterAll (fun () -> solve_conversion_subcomp flags fr);

    // clean location goals
    set_goals fgoals.fgoals_loca;
    iterAll (fun () -> exact (`LocationP))
  )


(*** Notations *)

unfold let usteel        = SH.unit_steel
unfold let usteel_atomic = SH.unit_steel_atomic
unfold let usteel_ghost  = SH.unit_steel_ghost


let to_steel
      (#[apply (`[])] flags : list flag)
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (r : unit ->
           MRepr a SH.KSteel (dummy_prog_tree a) (Some (Mkconv_index pre post req ens flags)) LocationP)
  : usteel a pre post req ens
  =
    let r : repr a SH.KSteel (dummy_prog_tree a) (Some (Mkconv_index pre post req ens flags)) LocationP
      = reify (r ()) in
    U.cast _ (SH.steel_u (ISome?.v r.repr_cv))

let to_steel_a
      (#[apply (`[])] flags : list flag)
      (#a : Type) (#opened : Mem.inames)
      (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (r : unit ->
           MRepr a (SH.KAtomic opened) (dummy_prog_tree a) (Some (Mkconv_index pre post req ens flags)) LocationP)
  : usteel_atomic a opened pre post req ens
  =
    let r : repr a (SH.KAtomic opened) (dummy_prog_tree a) (Some (Mkconv_index pre post req ens flags)) LocationP
      = reify (r ()) in
    U.cast _ (SH.atomic_u (ISome?.v r.repr_cv))

let to_steel_g
      (#[apply (`[])] flags : list flag)
      (#a : Type) (#opened : Mem.inames)
      (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (r : unit ->
           MReprGhost a opened (dummy_prog_tree a) (Some (Mkconv_index pre post req ens flags)) LocationP)
  : usteel_ghost a opened pre post req ens
  =
    let r : repr a (SH.KGhost opened) (dummy_prog_tree a) (Some (Mkconv_index pre post req ens flags)) LocationP
      = reify (r ()) in
    U.cast _ (SH.ghost_u (ISome?.v r.repr_cv))
