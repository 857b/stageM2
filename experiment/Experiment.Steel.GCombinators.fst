module Experiment.Steel.GCombinators

module U      = Learn.Util
module L      = FStar.List.Pure
module M      = Experiment.Steel.Repr.M
module MC     = Experiment.Steel.Combinators
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
module TLogic = Learn.Tactics.Logic

open Steel.Effect
open Steel.Effect.Atomic
open Experiment.Steel.VPropList
open Experiment.Steel.Interface
open FStar.Tactics
open Experiment.Steel.GCombinators.Lib

#set-options "--fuel 1 --ifuel 1"

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
        req (append_vars (vpl_sels_f p' sl_p0) (vpl_sels_f pre sl0._1)) (vpl_sels_f ro sl0._2))
      (fun sl_p0 sl0 x sl_p1 sl1 ->
        ens (append_vars (vpl_sels_f p' sl_p0) (vpl_sels_f pre sl0._1)) x
            (append_vars (vpl_sels_f p' sl_p1) (vpl_sels_f (post x) sl1._1)) (vpl_sels_f ro sl0._2) /\
        vpl_sels_f ro sl1._2 == vpl_sels_f ro sl0._2)
    begin fun () ->
      (**) steel_intro_vprop_of_list_append_f p' pre;
      let x = SH.ghost_u inner () in
      (**) steel_elim_vprop_of_list_append_f p' (post x);
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
      (cf : (Msk.filter_mask_split_l (L.length p') (L.length env) p' env;
             lin_cond_st L.(p' @ env) (let M.Mkrepr t _ = f in t)
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
