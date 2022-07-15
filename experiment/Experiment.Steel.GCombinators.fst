module Experiment.Steel.GCombinators

module U      = Learn.Util
module L      = FStar.List.Pure
module M      = Experiment.Steel.Repr.M
module LV     = Experiment.Steel.Repr.LV
module SF     = Experiment.Steel.Repr.SF
module SH     = Experiment.Steel.Steel
module Ll     = Learn.List
module Dl     = Learn.DList
module Fl     = Learn.FList
module SA     = Steel.Effect.Atomic
module Veq    = Experiment.Steel.VEquiv
module Msk    = Learn.List.Mask
module Mem    = Steel.Memory
module Perm   = Learn.Permutation
module LV2M   = Experiment.Steel.Repr.LV_to_M
module LV2SF  = Experiment.Steel.Repr.LV_to_SF
module SF2Fun = Experiment.Steel.Repr.SF_to_Fun
module TLogic = Learn.Tactics.Logic

open Steel.Effect
open Steel.Effect.Atomic
open Experiment.Steel.VPropList
open Experiment.Steel.Interface
open FStar.Tactics
open Experiment.Steel.GCombinators.Lib

#set-options "--fuel 1 --ifuel 1 --ide_id_info_off"

(**** slrewrite *)

/// [slrewrite x0 x1] will replace any occurrence of [x0] by [x1] in the current environment (using [l_to_r]).
/// Requires [x0 == x1].

[@@ __cond_solver__]
let slrewrite_spec_r (#t : Type u#t) (x0 x1 : t) (v0 v1 frame : vprop_list) (veq : squash (x0 == x1 ==> v0 == v1))
  : M.spec_r (U.unit' u#a)
  = M.Mkspec_r
       v0 (fun _ -> v1) frame
       (fun _ _ -> x0 == x1)
       (fun sl0 _ sl1 _ -> x0 == x1 /\ sl1 == sl0)

noeq
type slrewrite_gen_c (#t : Type u#t) (x0 x1 : t)
  : M.spec_r (U.unit' u#a) -> Type u#(max a 2) =
  | SlRewrite : (v0 : vprop_list) -> (v1 : vprop_list) -> (frame : vprop_list) ->
                (veq : squash (x0 == x1 ==> v0 == v1)) ->
                slrewrite_gen_c x0 x1 (slrewrite_spec_r x0 x1 v0 v1 frame veq)

let slrewrite_steel
      (opened : Mem.inames)
      (#t : Type u#t) (x0 x1 : t) (v0 v1 frame : vprop_list) (veq : squash (x0 == x1 ==> v0 == v1))
  : M.spc_steel_t (SH.KGhost opened) (slrewrite_spec_r u#t u#a x0 x1 v0 v1 frame veq)
  = SH.ghost_f #opened (fun () ->
    change_equal_slprop (vprop_of_list v0) (vprop_of_list v1);
    U.Unit'
  )

// TODO: put the unchanged vprop' in the frame
#push-options "--ifuel 0 --fuel 1"
[@@ __cond_solver__]
let __build_slrewrite
      (env : vprop_list)
      (#t : Type u#t) (x0 x1 : t) (#gen_tac : M.gen_tac_t)
      (env' : vprop_list)
      (rew : (rew_x : unit -> Lemma (x0 == x1)) -> squash (env == env'))
  : LV.lin_cond env (M.Tgen (U.unit' u#a) gen_tac (slrewrite_gen_c #t x0 x1)) (LV.csm_all env) (fun _ -> env')
  =
    introduce x0 == x1 ==> env == env'
      with _ . rew (fun () -> ());
    let s = slrewrite_spec_r x0 x1 env env' [] () in
    let sf : LV.gen_sf s =
      fun sl0 sl_ro ->
        introduce forall sl1 . Fl.flist_eq2 sl1 sl0 <==> sl1 == sl0
          with Fl.flist_eq2_spec sl1 sl0;
        SF.Tspec U.unit' (M.post_sl_t s.spc_post)
             (x0 == x1) (fun _ sl1 -> x0 == x1 /\ Fl.flist_eq2 sl1 sl0)
    in
    let pre_f : Perm.pequiv_list env (M.spc_pre1 s) = Perm.perm_f_to_list (Perm.pequiv_refl env) in
    Ll.list_extensionality (LV.gen_csm pre_f) (LV.csm_all env) (fun i ->
      let pre_f' = (LV.eij_split s.spc_pre s.spc_ro (LV.eij_of_perm_l pre_f))._1 in
      U.assert_by (L.index pre_f' i == i) (fun () ->
        Ll.splitAt_index (L.length env) (LV.eij_of_perm_l pre_f));
      L.lemma_index_memP pre_f' i
    );
    LV.LCgen env s (SlRewrite env env' [] ()) pre_f sf
#pop-options

let build_slrewrite (fr : flags_record) : Tac unit
  =
    apply (`__build_slrewrite);
    // rew
    let rew_x = intro () in
    l_to_r [binder_to_term rew_x];
    trefl ()

[@@ __repr_M__]
inline_for_extraction
let slrewrite (#t : Type u#t) (#opened : Mem.inames) (x0 x1 : t)
  : M.repr (SH.KGhost opened) (U.unit' u#a)
  =
    make_combinator (U.unit' u#a) (SH.KGhost opened) build_slrewrite (slrewrite_gen_c #t x0 x1)
      (fun _ (SlRewrite v0 v1 frame veq) -> slrewrite_steel opened x0 x1 v0 v1 frame veq)


(**** with_invariant_g *)

#push-options "--ifuel 0 --fuel 0"

// FIXME: raises warning 271 about theory symbols in pattern on the exists of ref_post
#push-options "--fuel 1 --warn_error -271"

/// A version of [with_invariant_g] with selectors.
inline_for_extraction
let with_invariant_g_sl
      (#a : Type)
      (pre : pre_t) (post : post_t a)
      (#opened : Mem.inames)
      (#p : vprop)
      (i : inv p { not (mem_inv opened i) })
      (req : t_of p -> t_of pre -> Type0) (ens : t_of p -> t_of pre -> (x : a) -> t_of p -> t_of (post x) -> Type0)
      (f : unit -> SteelGhost a (add_inv opened i)
                    (p `star` pre) (fun x -> p `star` (post x))
                    (requires fun h0      -> req (h0 p) (h0 pre))
                    (ensures  fun h0 x h1 -> ens (h0 p) (h0 pre) x (h1 p) (h1 (post x))))
  : SteelGhost a opened pre post
      (requires fun h0      -> forall (sl_p0 : t_of p) . req sl_p0 (h0 pre))
      (ensures  fun h0 x h1 -> exists (sl_p0 sl_p1 : t_of p) . ens sl_p0 (h0 pre) x sl_p1 (h1 (post x)))
  =
    let sl_pre = gget pre                                           in
    let ref_pre  (sl_pre' : t_of pre) : prop
      = sl_pre' == Ghost.reveal sl_pre                              in
    let ref_post (x : a) (sl_post : t_of (post x)) : prop
      = exists (sl_p0 sl_p1 : t_of p) . ens sl_p0 sl_pre x sl_p1 sl_post in
    intro_vrefine pre ref_pre;
    let x = SA.with_invariant_g
      #a #(vrefine pre ref_pre) #(fun x -> vrefine (post x) (ref_post x))
      #opened #p i
      (fun () -> begin
        let sl_p0   = gget p        in
        elim_vrefine pre ref_pre;
        let sl_pre' = gget pre      in
        U.assert_by (sl_pre' == sl_pre) (fun () ->
          assert (Ghost.reveal sl_pre' == Ghost.reveal sl_pre);
          Ghost.hide_reveal sl_pre;
          Ghost.hide_reveal sl_pre');
        eliminate forall (sl_p0 : t_of p) . req sl_p0 sl_pre
          with sl_p0;
        let x = f () in
        let sl_p1   = gget p        in
        let sl_post = gget (post x) in
        introduce exists (sl_p0 sl_p1 : t_of p) . ens sl_p0 sl_pre x sl_p1 sl_post
          with sl_p0 sl_p1 and ();
        intro_vrefine (post x) (ref_post x);
        x
      end <: SteelGhostT a (add_inv opened i)
               (p `star` vrefine pre ref_pre) (fun x -> p `star` vrefine (post x) (ref_post x)))
    in
    elim_vrefine (post x) (ref_post x);
    x

let change_equiv_slprop
      (#opened : Mem.inames)
      (p q : vprop)
      (l : unit -> Lemma (p `equiv` q))
  : SteelGhostT unit opened p (fun _ -> q)
  =
    rewrite_slprop p q (fun m -> l (); equiv_can_be_split p q; can_be_split_interp p q m)

/// A variant for changing [p] into an equivalent [vprop] (in practice a [vprop_of_list _]).
/// TODO? selector bijection instead : v <-> vprop_of_list (flatten_vprop _)
inline_for_extraction
let with_invariant_g_sl_list
      (#a : Type)
      (pre : pre_t) (post : post_t a)
      (#opened : Mem.inames)
      (#p : vprop)
      (i : inv p { not (mem_inv opened i) })
      (p' : vprop) (_ : squash (p `equiv` p'))//FIXME? Steel tactics fail if we put it as a refinement on p'
      (req : t_of p' -> t_of pre -> Type0) (ens : t_of p' -> t_of pre -> (x : a) -> t_of p' -> t_of (post x) -> Type0)
      (f : unit -> SteelGhost a (add_inv opened i)
                    (p' `star` pre) (fun x -> p' `star` (post x))
                    (requires fun h0      -> req (h0 p') (h0 pre))
                    (ensures  fun h0 x h1 -> ens (h0 p') (h0 pre) x (h1 p') (h1 (post x))))
  : SteelGhost a opened pre post
      (requires fun h0      -> forall (sl_p0 : t_of p') . req sl_p0 (h0 pre))
      (ensures  fun h0 x h1 -> exists (sl_p0 sl_p1 : t_of p') . ens sl_p0 (h0 pre) x sl_p1 (h1 (post x)))
  =
    let sl_pre = gget pre                                           in
    let ref_pre  (sl_pre' : t_of pre) : prop
      = sl_pre' == Ghost.reveal sl_pre                              in
    let ref_post (x : a) (sl_post : t_of (post x)) : prop
      = exists (sl_p0 sl_p1 : t_of p') . ens sl_p0 sl_pre x sl_p1 sl_post in
    intro_vrefine pre ref_pre;
    let x = SA.with_invariant_g
      #a #(vrefine pre ref_pre) #(fun x -> vrefine (post x) (ref_post x))
      #opened #p i
      (fun () -> begin
        change_equiv_slprop p p' (fun () -> ());
        slassert (p' `star` vrefine pre ref_pre);
        let sl_p0   = gget p'       in
        elim_vrefine pre ref_pre;
        let sl_pre' = gget pre      in
        (U.assert_by (sl_pre' == sl_pre) (fun () ->
          assert (Ghost.reveal sl_pre' == Ghost.reveal sl_pre);
          Ghost.hide_reveal sl_pre;
          Ghost.hide_reveal sl_pre');
        eliminate forall (sl_p0 : t_of p') . req sl_p0 sl_pre
          with sl_p0;
        ());
        let x = f () in
        let sl_p1   = gget p'       in
        let sl_post = gget (post x) in
        (introduce exists (sl_p0 sl_p1 : t_of p') . ens sl_p0 sl_pre x sl_p1 sl_post
          with sl_p0 sl_p1 and ();
        ());
        intro_vrefine (post x) (ref_post x);
        change_equiv_slprop p' p (fun () -> equiv_sym p p');
        x
      end <: SteelGhostT a (add_inv opened i)
               (p `star` vrefine pre ref_pre) (fun x -> p `star` vrefine (post x) (ref_post x)))
    in
    elim_vrefine (post x) (ref_post x);
    x

#pop-options


let with_invariant_inner_spec_r
     (#a : Type u#a) (p : vprop_list)
     (pre : M.pre_t) (post : M.post_t a) (ro : vprop_list)
     (req : sl_f L.(p @ pre) -> sl_f ro -> Type0)
     (ens : sl_f L.(p @ pre) -> (x : a) -> sl_f L.(p @ post x) -> sl_f ro -> Type0)
  : M.spec_r a
  = M.Mkspec_r L.(p @ pre) L.(fun x -> p @ post x) ro req ens

[@@ __cond_solver__]
let with_invariant_spec_r
     (#a : Type u#a) (p : vprop_list)
     (pre : M.pre_t) (post : M.post_t a) (ro : vprop_list)
     (req : sl_f L.(p @ pre) -> sl_f ro -> Type0)
     (ens : sl_f L.(p @ pre) -> (x : a) -> sl_f L.(p @ post x) -> sl_f ro -> Type0)
  : M.spec_r a
  =
    M.Mkspec_r
       pre post ro
       (fun sl0 sl_ro ->
          forall (sl_p0 : sl_f p) . req (append_vars sl_p0 sl0) sl_ro)
       (fun sl0 x sl1 sl_ro ->
         exists (sl_p0 sl_p1 : sl_f p) . ens (append_vars sl_p0 sl0) x (append_vars sl_p1 sl1) sl_ro)


(* Does not work (universes)
noeq
type with_invariant_gen_c
     (#a : Type u#a) (p : vprop) (f : M.prog_tree a)
  : M.spec_r a -> Type u#(max a 2) =
  | WithInvariant :
      (p' : vprop_to_list p) ->
      (env : vprop_list) -> (csm : LV.csm_t env) -> (prd : LV.prd_t a) ->
      (cf : LV.lin_cond L.(p' @ env) f (LV.bind_g_csm' p' csm) (fun x -> L.(p' @ prd x))) ->
      with_invariant_gen_c p f (with_invariant_spec_r_lc p' cf)
*)

/// [f] is mentioned only to be recovered by [__build_with_invariant]. Since it is a parameter, it does not
/// affect the universe of the datatype.
noeq
type with_invariant_gen_c (a : Type u#a) (ek : SH.effect_kind) (f : M.repr ek a) (p : vprop)
  : M.spec_r a -> Type u#(max a 2) =
  | WithInvariant :
      (p' : vprop_list) -> (tp : vprop_to_list p p') ->
      (pre : M.pre_t) -> (post : M.post_t a) -> (ro : vprop_list) ->
      (req : (sl_f L.(p' @ pre) -> sl_f ro -> Type0)) ->
      (ens : (sl_f L.(p' @ pre) -> (x : a) -> sl_f L.(p' @ post x) -> sl_f ro -> Type0)) ->
      (inner : M.spc_steel_t ek (with_invariant_inner_spec_r p' pre post ro req ens)) ->
      with_invariant_gen_c a ek f p (with_invariant_spec_r p' pre post ro req ens)


#push-options "--fuel 1 --z3rlimit 20"
inline_for_extraction
let with_invariant_g_steel
      (a : Type u#a) (opened : Mem.inames)
      (#p : vprop) (i : inv p{not (mem_inv opened i)})
      (p' : vprop_list) (tp : vprop_to_list p p')
      (pre : M.pre_t) (post : M.post_t a) (ro : vprop_list)
      (req : sl_f L.(p' @ pre) -> sl_f ro -> Type0)
      (ens : sl_f L.(p' @ pre) -> (x : a) -> sl_f L.(p' @ post x) -> sl_f ro -> Type0)
      (inner : M.spc_steel_t (SH.KGhost (add_inv opened i)) (with_invariant_inner_spec_r p' pre post ro req ens))
  : M.spc_steel_t (SH.KGhost opened) (with_invariant_spec_r p' pre post ro req ens)
  = SH.ghost_f #opened (fun () ->
    (**) (vprop_to_list_equiv tp; ());
    with_invariant_g_sl_list
      (vprop_of_list pre `star` vprop_of_list ro)
      (fun x -> vprop_of_list (post x) `star` vprop_of_list ro)
      i (vprop_of_list p') ()
      (fun sl_p0 sl0 ->
        req (append_vars sl_p0 sl0._1) sl0._2)
      (fun sl_p0 sl0 x sl_p1 sl1 ->
        ens (append_vars sl_p0 sl0._1) x
            (append_vars sl_p1 sl1._1) sl0._2 /\
        sl1._2 == sl0._2)
    begin fun () ->
      (**) intro_vpl_append p' pre;
      let x = SH.ghost_u inner () in
      (**) elim_vpl_append p' (post x);
      x
    end
  )
#pop-options

[@@ __cond_solver__]
let with_invariant_spec_r_lc
     (#a : Type u#a) (p : vprop_list) (#f : M.prog_tree a)
     (#env : vprop_list) (csm : LV.csm_t env) (#prd : LV.prd_t a)
     (cf : LV.lin_cond L.(p @ env) f (LV.bind_g_csm' p csm) L.(fun x -> p @ prd x))
  : M.spec_r a
  =
    (**) LV.filter_csm_bind_g_csm' p csm;
    (**) LV.filter_bind_g_csm'     p csm;
    with_invariant_spec_r p Msk.(filter_mask csm env) prd Msk.(filter_mask (mask_not csm) env)
                          (lc_req cf) (lc_ens cf)

// TODO? use __LV2SF__ operations instead of append_vars & split_vars
[@@ __LV2SF__]
let with_invariant_sf'
      (#a : Type u#a) (p : vprop_list) (#f : M.prog_tree a)
      (#env : vprop_list) (csm : LV.csm_t env) (#prd : LV.prd_t a)
      (cf : LV.lin_cond L.(p @ env) f (LV.bind_g_csm' p csm) L.(fun x -> p @ prd x))
      (sl0 : sl_f Msk.(filter_mask csm env)) (sl_ro : sl_f Msk.(filter_mask (mask_not csm) env))
  : SF.prog_tree a (M.post_sl_t prd)
  =
    (**) LV.filter_csm_bind_g_csm' p csm;
    (**) LV.filter_bind_g_csm'     p csm;
  SF.(
    Tbind _ _ (fun _ -> vprop_list_sels_t p) _
      (Tspec U.unit' (fun _ -> vprop_list_sels_t p) True (fun _ _ -> True)) (fun _ sl_p0 ->
   (Tbind _ _ L.(fun x -> vprop_list_sels_t (p @ prd x)) _
      (lc_sf cf (append_vars sl_p0 sl0) sl_ro) (fun x sl1' ->
      (Tret a x (M.post_sl_t prd) (Fl.dlist_of_f (split_vars p (prd x) sl1')._2))
  ))))


let force_tree_req #a (#post : SF.post_t a) (t : SF.prog_tree a post)
  : squash (SF.tree_req t <==> SF.tree_req t)
  = ()

let force_tree_ens #a (#post : SF.post_t a) (t : SF.prog_tree a post) x sl1
  : squash (SF.tree_ens t x sl1 <==> SF.tree_ens t x sl1)
  = ()

let __normal_with_invariant_sf : list norm_step = [
  delta_only [`%with_invariant_sf'; `%with_invariant_spec_r_lc; `%with_invariant_spec_r;
              `%M.Mkspec_r?.spc_req; `%M.Mkspec_r?.spc_ens; `%M.Mkspec_r?.spc_post;
              `%SF.tree_req; `%SF.tree_ens;
              `%SF.post_v; `%sl_f; `%lc_spec_r; `%lc_post; `%M.post_sl_t];
  iota; zeta; simplify
]

[@@ __LV2SF__]
let with_invariant_sf
      (#a : Type u#a) (p : vprop_list) (#f : M.prog_tree a)
      (#env : vprop_list) (csm : LV.csm_t env) (#prd : LV.prd_t a)
      (cf : LV.lin_cond L.(p @ env) f (LV.bind_g_csm' p csm) L.(fun x -> p @ prd x))
  : LV.gen_sf (with_invariant_spec_r_lc p csm cf)
  =
    fun sl0 sl_ro ->
      (**) LV.filter_csm_bind_g_csm' p csm;
      (**) LV.filter_bind_g_csm'     p csm;
      let t = with_invariant_sf' p csm cf sl0 sl_ro in
      let s = with_invariant_spec_r_lc p csm cf     in
      let rew_req sl0'
        : Lemma (SF.tree_req (lc_sf cf sl0' sl_ro) <==> lc_req cf sl0' sl_ro)
        = ()
      in
      assert (SF.tree_req t <==> s.spc_req sl0 sl_ro)
        by (norm __normal_with_invariant_sf;
            apply (`TLogic.rew_iff_left); apply (`force_tree_req);
            norm __normal_with_invariant_sf;
            apply (`TLogic.rew_iff_left );
              TLogic.rew_iff (fun r -> fail "");
            apply (`TLogic.rew_iff_right);
              TLogic.rew_iff (fun r -> apply (`rew_lc_sf_req));
            norm __normal_with_invariant_sf;
            smt ());

      introduce forall (x : a) (sl1 : sl_f (s.spc_post x)) .
                SF.tree_ens t x sl1 <==> s.spc_ens sl0 x sl1 sl_ro
      with begin
        U.assert_by_tac (fun () ->
            norm __normal_with_invariant_sf;
            apply (`TLogic.rew_iff_left); apply (`force_tree_ens);
            norm __normal_with_invariant_sf;
            apply (`TLogic.rew_iff_left);
              TLogic.rew_iff (fun r -> fail "");
              norm [];
            apply (`TLogic.exists_morph_iff); let sl_p0 = intro () in
            apply (`TLogic.rew_iff_right);
              TLogic.rew_iff (fun r -> apply (`rew_lc_sf_ens));
            apply (`TLogic.rew_iff_left);
              TLogic.rew_iff (fun r -> apply (`rew_exists_sl_f_app); r ());
              norm [];
            l_to_r [`append_split_vars]; norm [delta_only [`%Mktuple2?._2]; iota];
            norm __normal_with_invariant_sf;
            smt ()
        )
      end;

      t


[@@ __cond_solver__]
let __build_with_invariant
      (env : vprop_list)
      (#a : Type u#a) (#ek : SH.effect_kind) (f : M.repr ek a) (#p : vprop) (#gen_tac : M.gen_tac_t)
      (p' : vprop_list) (tp : vprop_to_list p p')
      (csm : LV.csm_t env) (prd : LV.prd_t a)
      (cf : (Msk.filter_mask_split_l p' env;
             lin_cond_st L.(p' @ env) f.repr_tree
               (Msk.mask_split_l (L.length p') (L.length env)) (fun _ -> p')
               csm prd))
  : LV.lin_cond env (M.Tgen a gen_tac (with_invariant_gen_c a ek f p)) csm prd
  =
    let n_p'  = L.length p'                 in
    let n_env = L.length env                in
    let csm0  = Msk.mask_split_l n_p' n_env in
    (**) LV.filter_csm_bind_g_csm' p' csm;
    (**) LV.filter_bind_g_csm'     p' csm;
    U.assert_by (Msk.mask_comp_or csm0 csm == LV.bind_g_csm' p' csm) (fun () ->
      LV.bind_g_csm'_as_comp_or p' csm);
    let pre = Msk.(filter_mask csm env)            in
    let ro  = Msk.(filter_mask (mask_not csm) env) in
    assert (lc_pre cf == L.(p' @ pre));
    assert (lc_ro  cf == ro);
    let s  = with_invariant_spec_r_lc p' csm cf    in
    let sf = with_invariant_sf        p' csm cf    in
    let pre_f : Perm.pequiv_list env (M.spc_pre1 s)
      = Perm.perm_f_to_list (Msk.mask_pequiv_append csm env)  in
    LV.gen_csm_pequiv_append env csm;
    assert (LV.gen_csm pre_f == csm);
    LV.LCgen env s
      (WithInvariant p' tp pre prd ro (lc_req cf) (lc_ens cf) (lc_to_spc_steel_t f cf))
      pre_f sf

let build_with_invariant_g (fr : flags_record) : Tac unit
  =
    let ctx () = [Info_location "in with_invariant_g"] in
    apply (`__build_with_invariant);
    // tp
    build_vprop_to_list fr ctx;
    // cf
    norm_lc ();
    build_lin_cond_st fr ctx


[@@ __repr_M__]
inline_for_extraction
let with_invariant_g
      (#a : Type u#a) (#opened : Mem.inames)
      (#p : vprop) (i : inv p{not (mem_inv opened i)})
      (f : M.repr (SH.KGhost (add_inv opened i)) a)
  : M.repr (SH.KGhost opened) a
  =
    make_combinator a (SH.KGhost opened)
      build_with_invariant_g (with_invariant_gen_c a (SH.KGhost (add_inv opened i)) f p)
      (fun _ (WithInvariant p' tp pre post ro req ens inner) ->
         with_invariant_g_steel a opened i p' tp pre post ro req ens inner)

#pop-options


(*** for_loop *)

module SU   = Learn.Steel.Util
module U32  = FStar.UInt32

#push-options "--ifuel 0 --fuel 1"
// We could give [U32.v start <= i] as an additional hypothesis
inline_for_extraction
let for_loop_sl
      (start : U32.t) (finish : U32.t { U32.v start <= U32.v finish })
      (inv  : (i : nat { i <= U32.v finish }) -> vprop)
      (invp : (i : nat { i <= U32.v finish }) -> t_of (inv i) -> Type0)
      (body : (i : U32.t { U32.v i < U32.v finish }) ->
              Steel unit (inv (U32.v i)) (fun () -> inv (U32.v i + 1))
                (requires fun h0      -> invp (U32.v i)     (h0 (inv (U32.v i))))
                (ensures  fun _ () h1 -> invp (U32.v i + 1) (h1 (inv (U32.v i + 1)))))
  : Steel unit (inv (U32.v start)) (fun () -> inv (U32.v finish))
      (requires fun h0      -> invp (U32.v  start) (h0 (inv (U32.v  start))))
      (ensures  fun _ () h1 -> invp (U32.v finish) (h1 (inv (U32.v finish))))
  =
    let inv_ref (i : nat {i <= U32.v finish}) (sl : t_of (inv i)) : prop
      = invp i sl /\True             in
    intro_vrefine (inv (U32.v start)) (inv_ref (U32.v start));
    Steel.Loops.for_loop start finish (fun i -> inv i `vrefine` inv_ref i)
    begin fun i ->
      elim_vrefine (inv (U32.v i)) (inv_ref (U32.v i));
      body i;
      intro_vrefine (inv (U32.v i + 1)) (inv_ref (U32.v i + 1))
    end;
    elim_vrefine (inv (U32.v finish)) (inv_ref (U32.v finish))
#pop-options

#push-options "--ifuel 0 --fuel 0"

let for_loop_preserve
      (finish : U32.t)
      (inv  : (i : nat { i <= U32.v finish }) -> vprop_list)
      (invp : (i : nat { i <= U32.v finish }) -> sl_f (inv i) -> Type0)
      (ro   : vprop_list)
      (req   : ((i : U32.t { U32.v i < U32.v finish }) -> sl_f (inv (U32.v i)) -> sl_f ro -> Type0))
      (ens   : ((i : U32.t { U32.v i < U32.v finish }) -> sl_f (inv (U32.v i)) -> sl_f (inv (U32.v i + 1)) ->
               sl_f ro -> Type0))
      (sl_ro : sl_f ro)
  : prop
  = forall (i : U32.t { U32.v i < U32.v finish }) (sl_inv0 : sl_f (inv (U32.v i))) .
    invp (U32.v i) sl_inv0 ==> (req i sl_inv0 sl_ro /\
   (forall (sl_inv1 : sl_f (inv (U32.v i + 1))) .
    ens i sl_inv0 sl_inv1 sl_ro ==> invp (U32.v i + 1) sl_inv1))

let elim_for_loop_preserve
      (finish : U32.t)
      (inv  : (i : nat { i <= U32.v finish }) -> vprop_list)
      (invp : (i : nat { i <= U32.v finish }) -> sl_f (inv i) -> Type0)
      (ro   : vprop_list)
      (req   : ((i : U32.t { U32.v i < U32.v finish }) -> sl_f (inv (U32.v i)) -> sl_f ro -> Type0))
      (ens   : ((i : U32.t { U32.v i < U32.v finish }) -> sl_f (inv (U32.v i)) -> sl_f (inv (U32.v i + 1)) ->
               sl_f ro -> Type0))
      (sl_ro : sl_f ro) (i : U32.t { U32.v i < U32.v finish }) (sl_inv0 : sl_f (inv (U32.v i)))
  : Lemma (requires for_loop_preserve finish inv invp ro req ens sl_ro /\
                    invp (U32.v i) sl_inv0)
          (ensures  req i sl_inv0 sl_ro /\
                   (forall (sl_inv1 : sl_f (inv (U32.v i + 1))) . {:pattern (ens i sl_inv0 sl_inv1 sl_ro)}
                    ens i sl_inv0 sl_inv1 sl_ro ==> invp (U32.v i + 1) sl_inv1))
  = ()

[@@ __LV2SF__]
inline_for_extraction
let for_loop_spec_r
      (start : U32.t) (finish : U32.t { U32.v start <= U32.v finish })
      (inv  : (i : nat { i <= U32.v finish }) -> vprop_list)
      (invp : (i : nat { i <= U32.v finish }) -> sl_f (inv i) -> Type0)
      (ro   : vprop_list)
      (lreq : sl_f ro -> Type0)
  : M.spec_r (U.unit' u#a)
  = M.Mkspec_r
        (inv (U32.v start)) (fun _ -> inv (U32.v finish)) ro
        (fun sl0 sl_ro -> invp (U32.v start) sl0 /\ lreq sl_ro)
        (fun _ _ sl1 _ -> invp (U32.v finish) sl1)

/// Since the weakest-precondition is (theoretically) not complete, we only require [lreq] to imply the preservation
/// of the invariant by the body of the loop.
noeq
type for_loop_gen_c
      (start : U32.t) (finish : U32.t { U32.v start <= U32.v finish })
      (inv  : (i : nat { i <= U32.v finish }) -> vprop_list)
      (invp : (i : nat { i <= U32.v finish }) -> sl_f (inv i) -> Type0)
      (body : (i : U32.t { U32.v i < U32.v finish }) -> M.repr u#a SH.KSteel U.unit')
  : M.spec_r (U.unit' u#a) -> Type u#(max a 2) =
  | ForLoop :
      (ro    : vprop_list) ->
      (req   : ((i : U32.t { U32.v i < U32.v finish }) -> sl_f (inv (U32.v i)) -> sl_f ro -> Type0)) ->
      (ens   : ((i : U32.t { U32.v i < U32.v finish }) -> sl_f (inv (U32.v i)) -> sl_f (inv (U32.v i + 1)) ->
               sl_f ro -> Type0)) ->
      (lreq  : (sl_ro : sl_f ro -> (rq : Type0 { rq ==> for_loop_preserve finish inv invp ro req ens sl_ro }))) ->
      (body' : ((i : U32.t { U32.v i < U32.v finish }) ->
               M.spc_steel_t u#a SH.KSteel #U.unit'
                 (M.Mkspec_r (inv (U32.v i)) (fun _ -> inv (U32.v i + 1)) ro
                             (req i) (fun sl0 _ sl1 sl_ro -> ens i sl0 sl1 sl_ro)))) ->
      for_loop_gen_c start finish inv invp body (for_loop_spec_r start finish inv invp ro lreq)

// ALT? can be defined directly on inv using pre_f : inv -> env{trg}
[@@ __cond_solver__]
let build_for_loop_pre_f
      (env : vprop_list) (inv : vprop_list) (pre_f : LV.eq_injection_l inv env)
  : Perm.pequiv_list env L.(inv @ Msk.(filter_mask (mask_not (LV.eij_trg_mask pre_f)) env))
  =
    let flt0 = Msk.(filter_mask (          LV.eij_trg_mask pre_f ) env) in
    let flt1 = Msk.(filter_mask (mask_not (LV.eij_trg_mask pre_f)) env) in
    let f0 : Perm.pequiv env L.(flt0 @ flt1)
        = Msk.mask_pequiv_append (LV.eij_trg_mask pre_f) env            in 
    let f1 : Perm.pequiv flt0 inv
        = LV.eij_equiv pre_f                                            in
    let f  : Perm.pequiv env L.(inv @ flt1)
        = Perm.(pequiv_trans f0 (pequiv_append f1 (pequiv_refl flt1)))  in
    (**) Perm.pequiv_as_eq f;
    Perm.perm_f_to_list f

#push-options "--z3rlimit 20"
let build_for_loop_pre_f_csm
      (env : vprop_list) (inv : vprop_list) (pre_f : LV.eq_injection_l inv env)
  : Lemma LV.(eij_trg_mask (eij_split inv Msk.(filter_mask (mask_not (LV.eij_trg_mask pre_f)) env)
                                      (build_for_loop_pre_f env inv pre_f))._1
           == eij_trg_mask pre_f)
  =
    let n0   = L.length inv                                             in
    let flt0 = Msk.(filter_mask (          LV.eij_trg_mask pre_f ) env) in
    let flt1 = Msk.(filter_mask (mask_not (LV.eij_trg_mask pre_f)) env) in
    let f    = build_for_loop_pre_f env inv pre_f                       in
    let f0   = (LV.eij_split inv flt1 f)._1                             in
    let csm0 = LV.eij_trg_mask pre_f                                    in
    let csm1 = LV.eij_trg_mask f0                                       in
    Ll.list_extensionality csm1 csm0 (fun j ->
      calc (<==>) {
        b2t (L.index csm1 j);
      <==> { Ll.memP_iff j f0 }
        exists (i : Fin.fin n0) . L.index f0 i == j;
      <==> { introduce forall (i : Fin.fin n0) . L.index f0 i == L.index pre_f i
           with begin
             L.lemma_index_memP pre_f i;
             calc (==) {
               L.index f0 i;
             == { Ll.splitAt_index n0 f }
               L.index f i;
             == {  }
               Msk.mask_perm_append csm0 (Msk.mask_push csm0 (L.index pre_f i));
             == { Msk.mask_perm_append_index csm0 (Msk.mask_push csm0 (L.index pre_f i)) }
               Msk.mask_pull csm0 (Msk.mask_push csm0 (L.index pre_f i));
             == { }
               L.index pre_f i;
             }
           end }
        exists (i : Fin.fin n0) . L.index pre_f i  == j;
      <==> { Ll.memP_iff j pre_f }
        L.index csm0 j;
      }
    )
#pop-options

let for_loop_body_lc
      (finish : U32.t)
      (inv  : (i : nat { i <= U32.v finish }) -> vprop_list)
      (ro   : vprop_list)
      (i    : U32.t { U32.v i < U32.v finish })
      (body : M.prog_tree U.unit')
  =
    LV.lin_cond L.(inv (U32.v i) @ ro) body
         (Msk.mask_split_l (L.length (inv (U32.v i))) (L.length ro)) (fun _ -> inv (U32.v i + 1))

let for_loop_body_lem
      (#finish : U32.t)
      (#inv  : (i : nat { i <= U32.v finish }) -> vprop_list)
      (#ro   : vprop_list)
      (#i    : U32.t { U32.v i < U32.v finish })
      (#body : M.prog_tree U.unit')
      (lc   : for_loop_body_lc finish inv ro i body)
  : Lemma (lc_pre lc == inv (U32.v i) /\ lc_ro lc == ro)
  =
    Msk.filter_mask_split_l (inv (U32.v i)) ro;
    Msk.filter_mask_split_r (inv (U32.v i)) ro

let for_loop_body_req
      (#finish : U32.t)
      (#inv  : (i : nat { i <= U32.v finish }) -> vprop_list)
      (#ro   : vprop_list)
      (#body : (i : U32.t { U32.v i < U32.v finish }) -> M.prog_tree U.unit')
      (lc   : (i : U32.t { U32.v i < U32.v finish }) -> for_loop_body_lc finish inv ro i (body i))
      (i : U32.t { U32.v i < U32.v finish })
  : sl_f (inv (U32.v i)) -> sl_f ro -> Type0
  = for_loop_body_lem (lc i); lc_req (lc i)

let for_loop_body_ens
      (#finish : U32.t)
      (#inv  : (i : nat { i <= U32.v finish }) -> vprop_list)
      (#ro   : vprop_list)
      (#body : (i : U32.t { U32.v i < U32.v finish }) -> M.prog_tree U.unit')
      (lc   : (i : U32.t { U32.v i < U32.v finish }) -> for_loop_body_lc finish inv ro i (body i))
      (i : U32.t { U32.v i < U32.v finish }) (sl0 : sl_f (inv (U32.v i)))
  : sl_f (inv (U32.v i + 1)) -> sl_f ro -> Type0
  = for_loop_body_lem (lc i); lc_ens (lc i) sl0 U.Unit'

[@@ __LV2SF__]
let for_loop_preserve_sf
      (#finish : U32.t)
      (#inv  : (i : nat { i <= U32.v finish }) -> vprop_list)
      (invp : (i : nat { i <= U32.v finish }) -> sl_f (inv i) -> Type0)
      (#ro   : vprop_list)
      (#body : (i : U32.t { U32.v i < U32.v finish }) -> M.prog_tree U.unit')
      (lc   : (i : U32.t { U32.v i < U32.v finish }) -> for_loop_body_lc finish inv ro i (body i))
      (sl_ro : sl_f ro)
  : Type0
  =
    forall (i : U32.t { U32.v i < U32.v finish }) .
      Fl.forall_flist (vprop_list_sels_t (inv (U32.v i))) (fun (sl_inv0 : sl_f (inv (U32.v i))) ->
      (**) for_loop_body_lem (lc i);
      invp (U32.v i) sl_inv0 ==> (
        lc_wp (lc i) sl_inv0 sl_ro (fun sl_inv1 -> invp (U32.v i + 1) sl_inv1.sel_v)))

let for_loop_preserve_sf_sound
      (#finish : U32.t)
      (#inv  : (i : nat { i <= U32.v finish }) -> vprop_list)
      (invp : (i : nat { i <= U32.v finish }) -> sl_f (inv i) -> Type0)
      (#ro   : vprop_list)
      (#body : (i : U32.t { U32.v i < U32.v finish }) -> M.prog_tree U.unit')
      (lc   : (i : U32.t { U32.v i < U32.v finish }) -> for_loop_body_lc finish inv ro i (body i))
      (sl_ro : sl_f ro)
  : Lemma (requires for_loop_preserve_sf invp lc sl_ro)
          (ensures  for_loop_preserve finish inv invp ro (for_loop_body_req lc) (for_loop_body_ens lc) sl_ro)
  =
    introduce forall (i : U32.t { U32.v i < U32.v finish }) (sl_inv0 : sl_f (inv (U32.v i))) .
                invp (U32.v i) sl_inv0 ==> (for_loop_body_req lc i sl_inv0 sl_ro /\
               (forall (sl_inv1 : sl_f (inv (U32.v i + 1))) .
                for_loop_body_ens lc i sl_inv0 sl_inv1 sl_ro ==> invp (U32.v i + 1) sl_inv1))
      with introduce _ ==> _ with _ .
    begin
      for_loop_body_lem (lc i);
      let wp = lc_wp (lc i) sl_inv0 sl_ro in
      let pt (sl_inv1 : SF2Fun.sl_tys_v ({val_t = U.unit'; sel_t = _})) = invp (U32.v i + 1) sl_inv1.sel_v in
      assert (wp pt);
      lc_wp_sound (lc i) sl_inv0 sl_ro pt
    end


#push-options "--z3rlimit 20"
[@@ LV.__lin_cond__]
let __build_for_loop
      (env : vprop_list)
      (start : U32.t) (finish : U32.t { U32.v start <= U32.v finish })
      (inv  : (i : nat { i <= U32.v finish }) -> vprop_list)
      (invp : (i : nat { i <= U32.v finish }) -> sl_f (inv i) -> Type0)
      (body : (i : U32.t { U32.v i < U32.v finish }) -> M.repr u#a SH.KSteel U.unit')
      (gen_tac : M.gen_tac_t)
      (pre_f : LV.eq_injection_l (inv (U32.v start)) env)
      (ro : vprop_list)
      (ro_eq : squash (ro == Msk.(filter_mask (mask_not (LV.eij_trg_mask pre_f)) env)))
      (pre_f' : Perm.pequiv_list env L.(inv (U32.v start) @ ro))
      (pre_f'_eq : squash (pre_f' == build_for_loop_pre_f env (inv (U32.v start)) pre_f))
      (lc_body : (i : U32.t { U32.v i < U32.v finish }) ->
                 (lc : for_loop_body_lc finish inv ro i (body i).repr_tree
                  { LV.lcsub_at_leaves lc}))
  : LV.lin_cond env (M.Tgen (U.unit' u#a) gen_tac (for_loop_gen_c start finish inv invp body))
                (LV.eij_trg_mask pre_f) (fun _ -> inv (U32.v finish))
  =
    let req  = for_loop_body_req lc_body                   in
    let ens  = for_loop_body_ens lc_body                   in
    let lreq (sl_ro : sl_f ro)
      : rq : Type0 { rq ==> for_loop_preserve finish inv invp ro req ens sl_ro }
      = FStar.Classical.move_requires (for_loop_preserve_sf_sound invp lc_body) sl_ro;
        for_loop_preserve_sf invp lc_body sl_ro                 in
    let s = for_loop_spec_r start finish inv invp ro lreq  in
    let body' (i : U32.t { U32.v i < U32.v finish })
      : M.spc_steel_t u#a SH.KSteel #U.unit'
                 (M.Mkspec_r (inv (U32.v i)) (fun _ -> inv (U32.v i + 1)) ro
                             (req i) (fun sl0 _ sl1 sl_ro -> ens i sl0 sl1 sl_ro))
      = for_loop_body_lem (lc_body i);
        lc_to_spc_steel_t (body i) (lc_body i)             in
    let sf : LV.gen_sf s = gen_sf_Tspec s                  in
    (**) build_for_loop_pre_f_csm env (inv (U32.v start)) pre_f;
    LV.LCgen env s (ForLoop ro req ens lreq body') pre_f' sf
#pop-options

let build_for_loop (fr : flags_record) : Tac unit
  =
    apply_raw (`__build_for_loop);
    // pre_f
    norm_lc ();
    build_eq_injection_l fr (fun () -> [Info_location "before the for loop"]);
    // ro
    dismiss ();
    norm_lc ();
    trefl ();
    // pre_f'
    dismiss ();
    norm [delta_only (L.append __delta_list (L.append __delta_perm [`%Msk.mask_pequiv_append; `%Perm.perm_f_cons]));
          delta_attr [`%__cond_solver__; `%Msk.__mask__; `%LV.__lin_cond__];
          delta_qualifier ["unfold"];
          iota; zeta; primops];
    trefl ();
    // lc_body
    let i = intro () in
    apply (`build_lcsub_at_leaves_lc);
    norm_lc ();
    build_lin_cond_exact fr (fun () -> [Info_location "in the for loop body"])


#push-options "--fuel 0 --ifuel 0"

// Quite long but even worse if we inline the body in the loop
#push-options  "--z3rlimit 40"
inline_for_extraction
let for_loop_steel_body
      (finish : U32.t)
      (inv  : (i : nat { i <= U32.v finish }) -> vprop_list)
      (invp : (i : nat { i <= U32.v finish }) -> sl_f (inv i) -> Type0)
      (ro   : vprop_list)
      (req  : (i : U32.t { U32.v i < U32.v finish }) -> sl_f (inv (U32.v i)) -> sl_f ro -> Type0)
      (ens  : ((i : U32.t { U32.v i < U32.v finish }) -> sl_f (inv (U32.v i)) -> sl_f (inv (U32.v i + 1)) ->
               sl_f ro -> Type0))
      (body : (i : U32.t { U32.v i < U32.v finish }) ->
               M.spc_steel_t u#a SH.KSteel #U.unit'
                 (M.Mkspec_r (inv (U32.v i)) (fun _ -> inv (U32.v i + 1)) ro
                             (req i) (fun sl0 _ sl1 sl_ro -> ens i sl0 sl1 sl_ro)))
      (ro0 : Ghost.erased (sl_f ro))
      (_ : squash (for_loop_preserve finish inv invp ro req ens ro0))
      (i : U32.t { U32.v i < U32.v finish })
  : Steel unit
      (vprop_of_list (inv (U32.v i)) `star` vprop_of_list ro)
      (fun () -> vprop_of_list (inv (U32.v i + 1)) `star` vprop_of_list ro)
      (requires fun h0      -> invp (U32.v i)     (sel_f (inv (U32.v i    )) h0) /\
                            sel_f ro h0 == Ghost.reveal ro0)
      (ensures  fun _ () h1 -> invp (U32.v i + 1) (sel_f (inv (U32.v i + 1)) h1) /\
                            sel_f ro h1 == Ghost.reveal ro0)
  =
    (**) let sl_i  = gget_f (inv (U32.v i)) in
    (**) let ro1   = gget_f ro              in
    (**) assert (ro1 == ro0);
    (**) elim_for_loop_preserve finish inv invp ro req ens ro0 i sl_i;
    (**) assert (req i sl_i ro1);
    let _ = SH.steel_u (body i) ()     in
    (**) let sl_i' = gget_f (inv (U32.v i + 1)) in
    (**) assert (ens i sl_i sl_i' ro0);
    SA.return ()
#pop-options

inline_for_extraction
let for_loop_steel
      (start : U32.t) (finish : U32.t { U32.v start <= U32.v finish })
      (inv  : (i : nat { i <= U32.v finish }) -> vprop_list)
      (invp : (i : nat { i <= U32.v finish }) -> sl_f (inv i) -> Type0)
      (ro   : vprop_list)
      (req  : (i : U32.t { U32.v i < U32.v finish }) -> sl_f (inv (U32.v i)) -> sl_f ro -> Type0)
      (ens  : ((i : U32.t { U32.v i < U32.v finish }) -> sl_f (inv (U32.v i)) -> sl_f (inv (U32.v i + 1)) ->
               sl_f ro -> Type0))
      (lreq : (sl_ro : sl_f ro -> (rq : Type0 { rq ==> for_loop_preserve finish inv invp ro req ens sl_ro })))
      (body : (i : U32.t { U32.v i < U32.v finish }) ->
               M.spc_steel_t u#a SH.KSteel #U.unit'
                 (M.Mkspec_r (inv (U32.v i)) (fun _ -> inv (U32.v i + 1)) ro
                             (req i) (fun sl0 _ sl1 sl_ro -> ens i sl0 sl1 sl_ro)))
  : M.spc_steel_t u#a SH.KSteel (for_loop_spec_r start finish inv invp ro lreq)
  = SH.steel_f (fun () ->
    let ro0 = gget_f ro in
    assert (for_loop_preserve finish inv invp ro req ens ro0);
    for_loop_sl start finish
      (fun i -> vprop_of_list (inv i) `star` vprop_of_list ro)
      (fun i sl -> invp i sl._1 /\ sl._2 == Ghost.reveal ro0)
      (for_loop_steel_body finish inv invp ro req ens body ro0 ());
    U.Unit'
  )
#pop-options


// TODO? it may be necessary to norm the [L.index] used in [sl_f (inv i)] in [invp]
// TODO? if vprop' was erasable, we could take as argument a [list (v : vprop {VUnit? v})] instead of a
//       [list vprop']
[@@ __repr_M__]
inline_for_extraction
let for_loop
      (start : U32.t) (finish : U32.t { U32.v start <= U32.v finish })
      (inv  : (i : nat { i <= U32.v finish }) -> vprop_list)
      (invp : (i : nat { i <= U32.v finish }) -> sl_f (inv i) -> Type0)
      (body : (i : U32.t { U32.v i < U32.v finish }) -> M.repr u#a SH.KSteel U.unit')
  : M.repr SH.KSteel (U.unit' u#a)
  =
    make_combinator (U.unit' u#a) SH.KSteel build_for_loop (for_loop_gen_c start finish inv invp body)
      (fun _ (ForLoop ro req ens lreq body') -> for_loop_steel start finish inv invp ro req ens lreq body')

#pop-options


(*** while_loop *)

// FIXME: this does not seems implementable with [Steel.Loops.while_loop]
(*
#push-options "--ifuel 0 --fuel 1"
inline_for_extraction
let while_loop_sl
      (inv  : vprop)
      (invp : t_of inv -> Type0)
      (#guard_post : post_t bool) (#guard_ens : t_of inv -> (b : bool) -> t_of (guard_post b) -> Type0)
      (guard : unit -> Steel bool inv guard_post
                 (requires fun h0      -> invp (h0 inv))
                 (ensures  fun h0 b h1 -> guard_ens (h0 inv) b (h1 (guard_post b))))
      (body  : unit -> Steel unit (guard_post true) (fun () -> inv)
                 (requires fun h0      -> exists (sl_inv : t_of inv) .
                                         invp sl_inv /\ guard_ens sl_inv true (h0 (guard_post true)))
                 (ensures  fun _ () h1 -> invp (h1 inv)))
  : Steel unit inv (fun () -> guard_post false)
      (requires fun h0      -> invp (h0 inv))
      (ensures  fun _ () h1 -> exists (sl_inv : t_of inv) .
                              invp sl_inv /\ guard_ens sl_inv false (h1 (guard_post false)))
  = ...
#pop-options
*)
