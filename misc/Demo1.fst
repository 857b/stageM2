module Demo1

module F   = Experiment.Steel.Monad
module M   = Experiment.Steel.Repr.M
module MC  = Experiment.Steel.Combinators
module SH  = Experiment.Steel.Steel
module GCb = Experiment.Steel.GCombinators
module U32 = FStar.UInt32
module Mem = Steel.Memory
module Vpl = Experiment.Steel.VPropList

open Steel.Effect.Common
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference

assume
val atomic_incr_u32 (#opened : Mem.inames) (r : ref U32.t)
  : SteelAtomic unit opened
      (vptr r) (fun _ -> vptr r)
      (requires fun h0 ->
          UInt.size (U32.v (sel r h0) + 1) U32.n)
      (ensures fun h0 _ h1 ->
          UInt.size (U32.v (sel r h0) + 1) U32.n /\ sel r h1 = U32.(sel r h0 +^ 1ul))

let ghost_gather_steel (a: Type0) opened p (r : ghost_ref a)
  : SteelGhost unit opened
      (Vpl.vprop_of_list [ghost_vptr' r (half_perm p); ghost_vptr' r (half_perm p)])
      (fun _ -> Vpl.vprop_of_list [ghost_vptr' r p])
      (fun _ -> True)
      (fun h0 _ h1 ->
        let sl0 = Vpl.sel_f [ghost_vptr' r (half_perm p); ghost_vptr' r (half_perm p)] h0 in
        let sl1 = Vpl.sel_f [ghost_vptr' r p] h1 in
        eq2 #a (sl0 1) (sl0 0) /\ eq2 #a (sl1 0) (sl0 0)
      )
  =
    (**) Vpl.elim_vpl_cons (ghost_vptr' r (half_perm p)) [ghost_vptr' r (half_perm p)];
    (**) Vpl.elim_vpl_cons (ghost_vptr' r (half_perm p)) [];
    ghost_gather #a #opened #p r;
    (**) Vpl.intro_vpl_cons (ghost_vptr' r p) []

[@@ F.__repr_M__]
let ghost_gather (#a : Type) (#opened : Mem.inames) (p : perm) (r : ghost_ref a)
  : M.repr (SH.KGhost opened) unit
  = MC.repr_of_steel_r ({
    spc_pre  = [ghost_vptr' r (half_perm p); ghost_vptr' r (half_perm p)];
    spc_post = (fun _ -> [ghost_vptr' r p]);
    spc_ro   = [];
    spc_req  = (fun _ _ -> True);
    spc_ens  = (fun sl0 _ sl1 _ -> eq2 #a (sl0 1) (sl0 0) /\ eq2 #a (sl1 0) (sl0 0));
  }) (SH.ghost_f (fun () -> ghost_gather_steel a opened p r))

let ghost_share_steel (a: Type0) opened p (r : ghost_ref a)
  : SteelGhost unit opened
      (Vpl.vprop_of_list [ghost_vptr' r p])
      (fun _ -> Vpl.vprop_of_list [ghost_vptr' r (half_perm p); ghost_vptr' r (half_perm p)])
      (fun _ -> True)
      (fun h0 _ h1 ->
        let sl0 = Vpl.sel_f [ghost_vptr' r p] h0 in
        let sl1 = Vpl.sel_f [ghost_vptr' r (half_perm p); ghost_vptr' r (half_perm p)] h1 in
        eq2 #a (sl1 0) (sl0 0) /\ eq2 #a (sl1 1) (sl0 0)
      )
  =
    (**) Vpl.elim_vpl_cons (ghost_vptr' r p) [];
    ghost_share #a #opened #p r;
    (**) Vpl.intro_vpl_cons (ghost_vptr' r (half_perm p)) [];
    (**) Vpl.intro_vpl_cons (ghost_vptr' r (half_perm p)) [ghost_vptr' r (half_perm p)]

[@@ F.__repr_M__]
let ghost_share (#a : Type) (#opened : Mem.inames) (p : perm) (r : ghost_ref a)
  : M.repr (SH.KGhost opened) unit
  = MC.repr_of_steel_r ({
    spc_pre  = [ghost_vptr' r p];
    spc_post = (fun _ -> [ghost_vptr' r (half_perm p); ghost_vptr' r (half_perm p)]);
    spc_ro   = [];
    spc_req  = (fun _ _ -> True);
    spc_ens  = (fun sl0 _ sl1 _ -> eq2 #a (sl1 0) (sl0 0) /\ eq2 #a (sl1 1) (sl0 0));
  }) (SH.ghost_f (fun () -> ghost_share_steel a opened p r))

unfold let perm2 = half_perm full_perm

[@@ __steel_reduce__]
let ghostp_sel (#a:Type) (#q:vprop) (r:ghost_ref a) (p : perm)
  (h:rmem q{FStar.Tactics.with_tactic selector_tactic (can_be_split q (ghost_vptrp r p) /\ True)})
  = h (ghost_vptrp r p)

[@@ __reduce__]
unfold
let inv_vp (r : ref U32.t) (r0 r1 : ghost_ref (Fin.fin 2))
  = vptr r `star` (ghost_vptrp r0 perm2 `star` ghost_vptrp r1 perm2)
[@@ __steel_reduce__]
let inv_rf (r : ref U32.t) (r0 r1 : ghost_ref (Fin.fin 2)) (sl : t_of (inv_vp r r0 r1))
  : prop
  = let sl_r  = sl._1    in
    let sl_r0 = sl._2._1 in
    let sl_r1 = sl._2._2 in
    U32.v sl_r == sl_r0 + sl_r1

let elim_inv #opened (r : ref U32.t) (r0 r1 : ghost_ref (Fin.fin 2))
  : SteelGhost unit opened
      (inv_vp r r0 r1 `vrefine` inv_rf r r0 r1)
      (fun _ -> inv_vp r r0 r1)
      (fun _ -> True) (ensures fun _ _ h1 -> U32.v (sel r h1) == ghostp_sel r0 perm2 h1 + ghostp_sel r1 perm2 h1)
  = elim_vrefine (inv_vp r r0 r1) (inv_rf r r0 r1)
let intro_inv #opened (r : ref U32.t) (r0 r1 : ghost_ref (Fin.fin 2))
  : SteelGhost unit opened
      (inv_vp r r0 r1)
      (fun _ -> inv_vp r r0 r1 `vrefine` inv_rf r r0 r1)
      (requires fun h0 -> U32.v (sel r h0) == ghostp_sel r0 perm2 h0 + ghostp_sel r1 perm2 h0) (fun _ _ _ -> True)
  = intro_vrefine (inv_vp r r0 r1) (inv_rf r r0 r1)

inline_for_extraction
let counter_OWG_aux
      (r : ref U32.t)
      (r0 r1 : ghost_ref (Fin.fin 2))
      (i : inv (inv_vp r r0 r1 `vrefine` inv_rf r r0 r1))
  : F.usteel unit (ghost_vptrp r0 perm2) (fun _ -> ghost_vptrp r0 perm2)
      (requires fun h0    -> h0 (ghost_vptrp r0 perm2) = 0)
      (ensures fun _ _ h1 -> h1 (ghost_vptrp r0 perm2) = 1)
  = F.(to_steel #[Timer; Dump Stage_WP] (
    GCb.with_invariant i (
      call_g (elim_inv r r0) r1;;
      ghost_gather full_perm r0;;
      call_a atomic_incr_u32 r;;
      call_g (ghost_write r0) 1;;
      ghost_share  full_perm r0;;
      call_g (intro_inv r r0) r1
    )
  ) ())
