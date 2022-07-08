module Learn.Steel.DLList.Impl

module U = Learn.Util

open FStar.List.Pure
open FStar.Ghost
open Steel.Effect
open Steel.Effect.Atomic
open Steel.Reference

include Learn.Steel.DLList.Param
include Learn.Steel.DLList.Data
include Learn.Steel.DLList.Derived

#set-options "--ide_id_info_off --ifuel 0 --fuel 1"


(**** [remove] *)

let fin_arg_pos (#n : nat) (i : Fin.fin n) : Lemma (n > 0) = ()

let remove (p : list_param) (r0 : ref p.r) (len : erased nat) (r1 : erased (ref p.r))
           (r : ref p.r) (i : erased (Fin.fin len))
  : Steel (ref p.r & erased (ref p.r)) // r0' & r1'
      (dllist p r0 len r1)
      (fun rs ->
        (**) fin_arg_pos i;
        vcell p r `star` dllist p rs._1 (len-1) rs._2)
      (requires fun h0 ->
        let sl0 = sel_dllist p r0 len r1 h0 in
        sl0.dll_prv == null /\ sl0.dll_nxt == null /\
        (index sl0.dll_sg i)._1 == r)
      (ensures  fun h0 rs h1 ->
        (**) fin_arg_pos i;
        let sl0 = sel_dllist p r0 len r1 h0 in
        index sl0.dll_sg i == (|r, g_data p r h1|) /\
        sel_dllist p rs._1 (len-1) rs._2 h1 `dll_eq3` (dll_remove i sl0)._3)
  =
    (**) let sl0 : erased (dllist_sel_t p r0 len r1) = gget (dllist p r0 len r1) in
    let rs = dllist_splitOn p r0 len r1 r i in
    (**) // if we try to use [i] directly as a length, the VC seems to contains parts equivalents
    (**) // to [Fin.fin len == nat]:
    (**) //    forall (k: int) (x: unit). pair (0 <= k) (k < reveal len) <==> equals (k >= 0) true;
    (**) let len0 : erased nat = hide (reveal i)   in
    (**) let len1 : erased nat = hide (len-i-1)    in
    (**) let rs0 = rs._1 in
    (**) let rs1 = rs._2 in
    (**) change_equal_slprop (dllist p r0 i rs._1) (dllist p r0 len0 rs0);
    (**) change_equal_slprop (dllist p rs._2 (len-i-1) r1) (dllist p rs1 len1 r1);
    let r1' = dllist_change_prv p rs1 len1 r1   rs0 in
    let r0' = dllist_change_nxt p r0  len0 rs0  rs1 in
    (**) intro_dllist_append p r0' len0 rs0 rs1 len1 r1';
    (**) dll_remove_eq i sl0;
    return (r0', r1')
