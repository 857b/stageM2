module Learn.Steel.List.Data

module L  = FStar.List.Pure
module G  = FStar.Ghost
module M  = Steel.Memory
module US = Learn.Steel.Util
open Steel.Memory
open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference

open Learn.Steel.List.DataD

#set-options "--fuel 1 --ifuel 0 --ide_id_info_off"

(* Separation logic predicate *)

let rec mlist_sl (#a : Type) (entry : ref (cell a)) (len : nat) (exit : ref (cell a))
  : Tot M.slprop (decreases %[len;0])
  = if len = 0 then M.pure (entry == exit)
    else M.h_exists #(cell a) (mcell_sl entry (len-1) exit)
and mcell_sl (#a : Type) (entry : ref (cell a)) (len' : nat) (exit : ref (cell a)) (c : cell a)
  : Tot M.slprop (decreases %[len';1])
  = pts_to_sl entry full_perm c `M.star` mlist_sl c.next len' exit


let mlist_sl_def (#a : Type) (entry : ref (cell a)) (len : nat) (exit : ref (cell a))
  : Lemma (mlist_sl #a entry len exit ==
      (if len = 0 then M.pure (entry == exit)
       else M.h_exists (mcell_sl entry (len-1) exit)))
  = normalize_term_spec (mlist_sl #a entry len exit)

let mlist_sl_S (#a : Type) (entry : ref (cell a)) (len : nat) (exit : ref (cell a))
  : Lemma (mlist_sl entry (len+1) exit == M.h_exists (mcell_sl entry len exit))
  =
    mlist_sl_def #a entry (len+1) exit

let mcell_sl_def (#a : Type) (entry : ref (cell a)) (len' : nat) (exit : ref (cell a)) (c : cell a)
  : Lemma (mcell_sl #a entry len' exit c == pts_to_sl entry full_perm c `M.star` mlist_sl c.next len' exit)
  = ()


(* Selector *)

#push-options "--ifuel 1"
let __begin_sg_entry = ()
let __end_sg_entry = ()
#pop-options

let rec mlist_sel' (#a : Type) (entry : ref (cell a)) (len : nat) (exit : ref (cell a))
                  (m : M.hmem (mlist_sl entry len exit))
  : GTot (mlist_sel_t entry len exit) (decreases len)
  = if len = 0 then begin
      pure_interp (entry == exit) m;
      []
    end else begin
      mlist_sl_def entry len exit;
      let c = M.id_elim_exists (mcell_sl entry (len - 1) exit) m in
      (entry, c.data) :: mlist_sel' c.next (len - 1) exit m
    end

let mlist_sel_def (#a : Type) (entry : ref (cell a)) (len : nat) (exit : ref (cell a))
                  (m : M.hmem (mlist_sl entry len exit))
  : Lemma (mlist_sel' #a entry len exit m ==
          (if len = 0 then []
           else begin
             mlist_sl_def entry len exit;
             let c = M.id_elim_exists (mcell_sl entry (len - 1) exit) m in
             (entry, c.data) :: mlist_sel' c.next (len - 1) exit m
           end))
  = ()

let mlist_sel_S (#a : Type) (entry : ref (cell a)) (len : nat) (exit : ref (cell a))
                (m : M.hmem (mlist_sl entry (len+1) exit))
  : Lemma (mlist_sl_S entry len exit; (
           mlist_sel' #a entry (len+1) exit m ==
          (let c = M.id_elim_exists (mcell_sl entry len exit) m in
           (entry, c.data) :: mlist_sel' c.next len exit m
           )))
  =
    mlist_sl_def entry (len+1) exit;
    mlist_sl_S   entry  len    exit;
    mlist_sel_def #a entry (len+1) exit m


let rec mlist_sel_depends_only_on (#a : Type) entry len exit
        (m0 : M.hmem (mlist_sl #a entry len exit)) (m1 : M.mem{disjoint m0 m1})
  : Lemma (ensures mlist_sel' entry len exit m0 == mlist_sel' entry len exit (join m0 m1))
          (decreases len)
  = 
    if len = 0 then ()
    else begin
      mlist_sl_def entry len exit;
      let c0 = G.reveal (M.id_elim_exists (mcell_sl entry (len - 1) exit) m0)           in
      let c1 = G.reveal (M.id_elim_exists (mcell_sl entry (len - 1) exit) (join m0 m1)) in
      US.pts_to_ref_injective_and entry full_perm c0 c1 (join m0 m1);
      calc (==) {
        mlist_sel' entry len exit m0;
      == {mlist_sel_def entry len exit m0}
        (entry, c0.data) :: mlist_sel' c0.next (len - 1) exit m0;
      == {mlist_sel_depends_only_on c0.next (len - 1) exit m0 m1}
        (entry, c1.data) :: mlist_sel' c1.next (len - 1) exit (join m0 m1);
      == {mlist_sel_def entry len exit (join m0 m1)}
        mlist_sel' entry len exit (join m0 m1);
      }
    end

let rec mlist_sel_depends_only_on_core(#a : Type) entry len exit
        (m0 : M.hmem (mlist_sl #a entry len exit))
  : Lemma (ensures mlist_sel' entry len exit m0 == mlist_sel' entry len exit (core_mem m0))
          (decreases len)
  =
    if len = 0 then ()
    else begin
      mlist_sl_def entry len exit;
      let c0 = G.reveal (M.id_elim_exists (mcell_sl entry (len - 1) exit) m0)            in
      let c1 = G.reveal (M.id_elim_exists (mcell_sl entry (len - 1) exit) (core_mem m0)) in
      US.pts_to_ref_injective_and entry full_perm c0 c1 (core_mem m0);
      calc (==) {
        mlist_sel' entry len exit m0;
      == {mlist_sel_def entry len exit m0}
        (entry, c0.data) :: mlist_sel' c0.next (len - 1) exit m0;
      == {mlist_sel_depends_only_on_core c0.next (len - 1) exit m0}
        (entry, c1.data) :: mlist_sel' c1.next (len - 1) exit (core_mem m0);
      == {mlist_sel_def entry len exit (core_mem m0)}
        mlist_sel' entry len exit (core_mem m0);
      }
    end

let mlist_sel #a entry len exit  =
  Classical.forall_intro_2 (mlist_sel_depends_only_on      entry len exit);
  Classical.forall_intro   (mlist_sel_depends_only_on_core entry len exit);
  mlist_sel' #a entry len exit


(* intro/elim lemmas *)

let intro_mlist_nil_lem (#a : Type) (r0 : ref (cell a)) (m : mem)
  : Lemma (ensures  interp (hp_of (mlist r0 0 r0)) m /\
                    mlist_sel r0 0 r0 m == [])
  =
    pure_interp (r0 == r0) m;
    mlist_sl_def r0 0 r0

let intro_mlist_nil (#a : Type) #opened (r0 : ref (cell a))
  : SteelGhost unit opened
      emp (fun () -> mlist r0 0 r0)
      (requires fun _ -> True) (ensures fun _ () h1 -> sel_list r0 0 r0 h1 == [])
  =
    change_slprop_rel
      emp (mlist r0 0 r0)
      (fun _ l -> l == []) (intro_mlist_nil_lem r0)


let elim_mlist_nil_lem (#a : Type) (r0 r1 : ref (cell a)) (m : mem)
  : Lemma (requires interp (hp_of (mlist r0 0 r1)) m)
          (ensures  interp (hp_of emp) m /\ r0 == r1)
  =
    mlist_sl_def r0 0 r1;
    pure_interp (r0 == r1) m;
    reveal_emp ();
    M.intro_emp m

let elim_mlist_nil (#a : Type) #opened (r0 : ref (cell a)) (r1 : ref (cell a))
  : SteelGhost unit opened
      (mlist r0 0 r1) (fun () -> emp)
      (requires fun _ -> True) (ensures fun _ () _ -> r0 == r1)
  =
     change_slprop_rel
      (mlist r0 0 r1) emp
      (fun _ _ -> r0 == r1) (elim_mlist_nil_lem r0 r1)


#push-options "--fuel 2"
let intro_mlist_cons_lem (#a : Type) (r0 r1 : ref (cell a)) (x : a) (len : nat) (exit : ref (cell a)) (m : mem)
  : Lemma (requires interp (hp_of (pts_to r0 full_perm ({next = r1; data = x}) `star` mlist r1 len exit)) m)
          (ensures  interp (hp_of (mlist r0 (len + 1) exit)) m /\
                    mlist_sel r0 (len + 1) exit m == (r0, x) :: mlist_sel r1 len exit m)
  =
    intro_h_exists ({next=r1; data=x}) (mcell_sl r0 len exit) m;
    assert (interp (M.h_exists (mcell_sl r0 len exit)) m);
    mlist_sl_S r0 len exit;

    let c = {next = r1; data = x} in
    assert (interp (pts_to_sl r0 full_perm c) m);
    let c' = G.reveal (M.id_elim_exists (mcell_sl r0 len exit) m) in
    US.pts_to_ref_injective_and r0 full_perm c c' m;
    mlist_sel_S r0 len exit m
#pop-options

let intro_mlist_cons' (#a : Type) #opened (r0 r1 : ref (cell a)) (x : a) (len : nat) (exit : ref (cell a))
  : SteelGhost unit opened
     (vptr r0 `star` mlist r1 len exit)
     (fun () -> mlist r0 (len + 1) exit)
     (requires fun h0 -> sel r0 h0 == {next = r1; data = x})
     (ensures fun h0 () h1 -> sel_list r0 (len + 1) exit h1 == (r0, x) :: sel_list r1 len exit h0)
  =
    let _ = elim_vptr r0 full_perm in
    change_slprop_rel
      (pts_to r0 full_perm ({next = r1; data = x}) `star` mlist r1 len exit)
      (mlist r0 (len + 1) exit)
      (fun (_, l0) l1 -> l1 == (r0, x) :: l0)
      (intro_mlist_cons_lem r0 r1 x len exit)

let intro_mlist_cons (#a : Type) #opened (r0 r1 : ref (cell a)) (len : nat) (exit : ref (cell a))
  : SteelGhost unit opened
     (vptr r0 `star` mlist r1 len exit)
     (fun () -> mlist r0 (len + 1) exit)
     (requires fun h0 -> (sel r0 h0).next == r1)
     (ensures fun h0 () h1 -> sel_list r0 (len + 1) exit h1
                           == (r0, (sel r0 h0).data) :: sel_list r1 len exit h0)
  =
    let c = gget (vptr r0) in
    intro_mlist_cons' r0 r1 c.data len exit


let elim_mlist_cons_lem (#a : Type) (r0 : ref (cell a)) (hd : ref (cell a) & a) (tl : list (ref (cell a) & a))
                        (len : nat) (exit : ref (cell a)) (m: mem)
  : Lemma (requires interp (hp_of (mlist r0 (len + 1) exit)) m /\ mlist_sel r0 (len + 1) exit m == hd :: tl)
          (ensures (let r1 = sg_entry tl exit in
                    let q  = pts_to r0 full_perm ({next = r1; data = hd._2}) `star` mlist r1 len exit in
                    interp (hp_of q) m /\
                    (sel_of q m <: unit & mlist_sel_t r1 len exit) == ((), tl)))
  =
    mlist_sl_S r0 len exit;
    mlist_sel_S r0 len exit m;
    let c = M.id_elim_exists (mcell_sl r0 len exit) m in
    let r1 = sg_entry tl exit in
    let q  = pts_to r0 full_perm ({next = r1; data = hd._2}) `star` mlist r1 len exit in
    assert (hd._1  == r0);
    assert (G.reveal c == {next = r1; data = hd._2});
    assert (interp (mcell_sl r0 len exit c) m);
    mcell_sl_def r0 len exit c;
    assert (interp (pts_to_sl r0 full_perm c `M.star` mlist_sl c.next len exit) m);
    assert_norm (interp (pts_to_sl r0 full_perm c `M.star` mlist_sl c.next len exit) m
              <==> interp (hp_of (pts_to r0 full_perm c `star` mlist c.next len exit)) m);
    assert (interp (hp_of q) m);
 
    let sl0 = mlist_sel c.next len exit m in
    assert (mlist_sel r0 (len + 1) exit m == (r0, c.data) :: sl0);
    let sl1 = mlist_sel r1 len exit m in
    assert (sl0 == sl1);
    assert_norm (sel_of q m == ((), sl1))

let elim_mlist_cons (#a : Type) #opened (r0 : ref (cell a)) (len : nat) (exit : ref (cell a))
  : SteelGhost (G.erased (ref (cell a))) opened
     (mlist r0 (len + 1) exit)
     (fun r1 -> vptr r0 `star` mlist r1 len exit)
     (requires fun _ -> True)
     (ensures  fun h0 r1 h1 ->
      (let l = sel_list r0 (len+1) exit h0 in
       G.reveal r1 == sg_entry (L.tl l) exit /\
       sel r0 h1 == {next = r1; data = (L.hd l)._2} /\
       sel_list r1 len exit h1 == L.tl l))
  =
    let (l : G.erased (t_of (mlist r0 (len+1) exit))) = gget (mlist r0 (len+1) exit) in
    let (l : mlist_sel_t r0 (len+1) exit) = G.reveal l in
    let hd :: tl = l in
    let r1 = sg_entry tl exit in
    change_slprop
      (mlist r0 (len + 1) exit)
      (pts_to r0 full_perm ({next = r1; data = hd._2}) `star` mlist r1 len exit)
      (G.hide (hd :: tl)) (G.hide ((), tl))
      (elim_mlist_cons_lem r0 hd tl len exit);
    intro_vptr r0 full_perm ({next = r1; data = hd._2});
    r1
