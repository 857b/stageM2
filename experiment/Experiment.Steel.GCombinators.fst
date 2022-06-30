module Experiment.Steel.GCombinators

module U    = Learn.Util
module L    = FStar.List.Pure
module M    = Experiment.Steel.Repr.M
module MC   = Experiment.Steel.Combinators
module LV   = Experiment.Steel.Repr.LV
module SF   = Experiment.Steel.Repr.SF
module SH   = Experiment.Steel.Steel
module Ll   = Learn.List
module Fl   = Learn.FList
module Veq  = Experiment.Steel.VEquiv
module Mem  = Steel.Memory
module Perm = Learn.Permutation

open Steel.Effect
open Steel.Effect.Atomic
open Experiment.Steel.VPropList
open Experiment.Steel.Interface
open FStar.Tactics
open Experiment.Steel.Tac

#set-options "--fuel 1 --ifuel 1"

#push-options "--fuel 0 --ifuel 0"
//TODO? inline s
inline_for_extraction
let make_combinator_steel_ghost
      (#a : Type u#a) (opened : Mem.inames) (s : M.spec_r a) (f : M.spc_steel_t (SH.KGhost opened) s)
      (#pre : M.pre_t) (pre_eq : Veq.vequiv pre (M.spc_pre1 s))
      (#post : M.post_t a) (post_eq : ((x : a) -> Veq.vequiv (M.spc_post1 s x) (post x)))
  : M.repr_steel_t (SH.KGhost opened) a pre post (M.gen_req s pre_eq post_eq) (M.gen_ens s pre_eq post_eq)
  =
    SH.ghost_f #opened (fun () ->
      pre_eq.veq_g _;
      (**) steel_elim_vprop_of_list_append_f s.spc_pre s.spc_ro;
      (**) let sl0'  = gget_f s.spc_pre in
      (**) let sl_ro = gget_f s.spc_ro in     
      (**) assert (s.spc_req sl0' sl_ro);
      let (x : a) = SH.ghost_u f () in
      (**) let sl1'   = gget_f (s.spc_post x) in
      (**) let sl_ro' = gget_f s.spc_ro       in
      (**) assert (sl_ro' == sl_ro);
      (**) assert (s.spc_ens sl0' x sl1' sl_ro);
      (**) steel_intro_vprop_of_list_append_f (s.spc_post x) s.spc_ro;
      (post_eq x).veq_g _;
      x
    )
#pop-options
    

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
let slrewrite_M_tree (#t : Type u#t) (x0 x1 : t)
  : M.prog_tree (U.unit' u#a)
  = M.Tgen (U.unit' u#a) build_slrewrite (slrewrite_gen_c #t x0 x1)

[@@ __repr_M__]
inline_for_extraction
let slrewrite (#t : Type u#t) (#opened : Mem.inames) (x0 x1 : t)
  : M.repr (SH.KGhost opened) (U.unit' u#a)
  = {
    repr_tree  = slrewrite_M_tree x0 x1;
    repr_steel = (fun pre post c ->
                    let M.TCgen s sh _ pre_eq _ post_eq = c in
                    let SlRewrite v0 v1 frame veq = U.cast (slrewrite_gen_c #t x0 x1 s) sh in
                    make_combinator_steel_ghost opened s
                      (slrewrite_steel opened x0 x1 v0 v1 frame veq)
                      pre_eq post_eq)
  }


module F   = Experiment.Steel.Notations
module U32 = FStar.UInt32
open Steel.Reference

let test_slrewrite (r0 r1 r2 : ref U32.t)
  : F.steel unit
      (vptr r0 `star` vptr r1) (fun _ -> vptr r2 `star` vptr r1)
      (requires fun _ -> r0 == r2)
      (ensures  fun h0 _ h1 -> sel r0 h0 == sel r2 h1 /\ sel r1 h0 == sel r1 h1)
  = F.(to_steel (
      MC.ghost_to_steel_ct (slrewrite r0 r2) (fun _ -> U.Unit');;
      return ()
    ) ())
