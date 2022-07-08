module Learn.Steel.DLList.Derived

module U   = Learn.Util
module G   = FStar.Ghost
module Ll  = Learn.List
module SU  = Learn.Steel.Util
module Mem = Steel.Memory

open FStar.List.Pure
open Steel.Effect
open Steel.Effect.Atomic
open Steel.Reference

include Learn.Steel.DLList.Param
include Learn.Steel.DLList.Data

#set-options "--ide_id_info_off --ifuel 1 --fuel 1"


(*** Operations on [dllist_sel_t] *)

let dll_len (#p : list_param) (#r0 : ref p.r) (#len : nat) (#r1 : ref p.r) (sl : dllist_sel_t p r0 len r1)
  : nat
  = len

let dll_entry (#p : list_param) (#r0 : ref p.r) (#len : nat) (#r1 : ref p.r) (sl : dllist_sel_t p r0 len r1)
  : ref p.r
  = r0

let dll_exit (#p : list_param) (#r0 : ref p.r) (#len : nat) (#r1 : ref p.r) (sl : dllist_sel_t p r0 len r1)
  : ref p.r
  = r1

unfold
let dll_eq3 #p #r0 #len #r1 (sl : dllist_sel_t p r0 len r1) #r0' #len' #r1' (sl' : dllist_sel_t p r0' len' r1')
  : prop
  = r0 == r0' /\ len == len' /\ r1 == r1' /\ sl == sl'


let sg_entry_index (#p : list_param) (l : list (cell_t p)) (nxt : ref p.r)
  : Lemma (sg_entry l nxt == (if length l > 0 then (index l 0)._1 else nxt))
  = ()

let sg_exit_index (#p : list_param) (prv : ref p.r) (l : list (cell_t p))
  : Lemma (sg_exit prv l == (if length l > 0 then (index l (length l - 1))._1 else prv))
  = if Cons? l then Ll.last_index l


let dll_change_nxt #p #r0 #len #r1 (sl : dllist_sel_t p r0 len r1) (nxt : ref p.r)
  : dllist_sel_t p (sg_entry sl.dll_sg nxt) len r1
  = {sl with dll_nxt = nxt}

let dll_change_prv #p #r0 #len #r1 (sl : dllist_sel_t p r0 len r1) (prv : ref p.r)
  : dllist_sel_t p r0 len (sg_exit prv sl.dll_sg)
  = {sl with dll_prv = prv}


(***** [dll_tail] *)

let dll_nxt0 (#p : list_param) (#r0 : ref p.r) (#len : nat {len > 0}) (#r2 : ref p.r) (sl0 : dllist_sel_t p r0 len r2)
  : ref p.r
  = sg_entry (tl sl0.dll_sg) sl0.dll_nxt

val dll_tail_lem
      (#p : list_param) (#r0 : ref p.r) (#len : nat {len > 0}) (#r2 : ref p.r) (sl0 : dllist_sel_t p r0 len r2)
  : Lemma (sg_exit r0 (tl sl0.dll_sg) == r2)

let dll_tail
      (#p : list_param) (#r0 : ref p.r) (#len : nat {len > 0}) (#r2 : ref p.r) (sl0 : dllist_sel_t p r0 len r2)
  : dllist_sel_t p (dll_nxt0 sl0) (len-1) r2
  =
    (**) dll_tail_lem sl0;
    {
      dll_sg  = tl sl0.dll_sg;
      dll_prv = r0;
      dll_nxt = sl0.dll_nxt;
    }

let dll_tail_cons
      (#p : list_param) (#r0 #r1 : ref p.r) (#len' : nat) (#r2 : ref p.r)
      (c : t_of (vcell p r0))
      (sl1 : dllist_sel_t p r1 len' r2 {sl1.dll_prv == r0})
  : Lemma (dll_tail (dll_cons c sl1) == sl1) [SMTPat (dll_tail (dll_cons c sl1))]
  = ()


(***** [dll_snoc] *)

let dll_snoc
      (#p : list_param) (#r0 : ref p.r) (#len : nat) (#r1 #r2 : ref p.r)
      (sl : dllist_sel_t p r0 len r1 {sl.dll_nxt == r2})
      (c  : t_of (vcell p r2))
  : GTot (dllist_sel_t p r0 (len + 1) r2)
  =
    let sg_c = (|r2, (p.cell r2).get_data c|) in
    (**) lemma_append_last sl.dll_sg [sg_c];
    (**) assert_norm (length [sg_c] == 1);
    {
      dll_sg  = snoc (sl.dll_sg, sg_c);
      dll_prv = sl.dll_prv;
      dll_nxt = (p.cell r2).get_ref c Forward;
    }


(***** [dll_init] *)

let dll_prv0 (#p : list_param) (#r0 : ref p.r) (#len : nat {len > 0}) (#r2 : ref p.r) (sl : dllist_sel_t p r0 len r2)
  : ref p.r
  = sg_exit sl.dll_prv (init sl.dll_sg)

let dll_init
      (#p : list_param) (#r0 : ref p.r) (#len : nat {len > 0}) (#r2 : ref p.r) (sl : dllist_sel_t p r0 len r2)
  : dllist_sel_t p r0 (len-1) (dll_prv0 sl)
  =
    {
      dll_sg  = init sl.dll_sg;
      dll_prv = sl.dll_prv;
      dll_nxt = r2;
    }

let dll_init_snoc
      (#p : list_param) (#r0 : ref p.r) (#len : nat) (#r1 r2 : ref p.r)
      (sl : dllist_sel_t p r0 len r1 {sl.dll_nxt == r2})
      (c  : t_of (vcell p r2))
  : Lemma (dll_prv0 (dll_snoc sl c) == r1 /\ dll_init (dll_snoc sl c) == sl)
  =
    let sg_c = (|r2, (p.cell r2).get_data c|) in
    Ll.unsnoc_eq_init (snoc (sl.dll_sg, sg_c))


(***** [dll_append] *)


val dll_append_lem
      (#p : list_param) (#r0 : ref p.r) (#len0 : nat) (#r1 #r2 : ref p.r) (#len1 : nat) (#r3 : ref p.r)
      (sl0 : dllist_sel_t p r0 len0 r1 { sl0.dll_nxt == r2 })
      (sl1 : dllist_sel_t p r2 len1 r3 { sl1.dll_prv == r1 })
  : Lemma (sg_entry (sl0.dll_sg @ sl1.dll_sg) sl1.dll_nxt == r0 /\
           sg_exit  sl0.dll_prv (sl0.dll_sg @ sl1.dll_sg) == r3)

let dll_append
      (#p : list_param) (#r0 : ref p.r) (#len0 : nat) (#r1 #r2 : ref p.r) (#len1 : nat) (#r3 : ref p.r)
      (sl0 : dllist_sel_t p r0 len0 r1 { sl0.dll_nxt == r2 })
      (sl1 : dllist_sel_t p r2 len1 r3 { sl1.dll_prv == r1 })
  : dllist_sel_t p r0 (len0+len1) r3
  =
    (**) dll_append_lem sl0 sl1;
    {
      dll_sg  = sl0.dll_sg @ sl1.dll_sg;
      dll_prv = sl0.dll_prv;
      dll_nxt = sl1.dll_nxt
    }

let dll_append_cons
      (p : list_param) (r0 r0' : ref p.r) (len0 : nat) (r1 r2 : ref p.r) (len1 : nat) (r3 : ref p.r)
      (c   : t_of (vcell p r0))
      (sl0 : dllist_sel_t p r0' len0 r1 { sl0.dll_prv == r0 /\ sl0.dll_nxt == r2 })
      (sl1 : dllist_sel_t p r2  len1 r3 { sl1.dll_prv == r1 })
  : Lemma (dll_append (dll_cons c sl0) sl1 == dll_cons c (dll_append sl0 sl1))
  = ()

val dll_tail_append
      (#p : list_param) (#r0 : ref p.r) (#len0 : nat) (#r1 #r2 : ref p.r) (#len1 : nat) (#r3 : ref p.r)
      (sl0 : dllist_sel_t p r0 len0 r1 { sl0.dll_nxt == r2 /\ len0 > 0})
      (sl1 : dllist_sel_t p r2 len1 r3 { sl1.dll_prv == r1 })
  : Lemma (dll_nxt0 (dll_append sl0 sl1) == dll_nxt0 sl0 /\
           dll_tail (dll_append sl0 sl1) == dll_append (dll_tail sl0) sl1)

(***** [dll_sglt] *)

#push-options "--fuel 2"

let dll_sglt (#p : list_param) (#r : ref p.r) (c : t_of (vcell p r))
  : GTot (dllist_sel_t p r 1 r)
  = {
    dll_sg  = [(|r, (p.cell r).get_data c|)];
    dll_prv = (p.cell r).get_ref c Backward;
    dll_nxt = (p.cell r).get_ref c Forward;
  }

let dll_cons_as_append
      (#p : list_param) (#r0 #r1 : ref p.r) (#len' : nat) (#r2 : ref p.r)
      (c : t_of (vcell p r0) {(p.cell r0).get_ref c Forward == r1})
      (sl : dllist_sel_t p r1 len' r2 {sl.dll_prv == r0})
  : Lemma (c `dll_cons` sl == dll_sglt c `dll_append` sl)
  = ()

let dll_snoc_as_append
      (#p : list_param) (#r0 : ref p.r) (#len : nat) (#r1 #r2 : ref p.r)
      (sl : dllist_sel_t p r0 len r1 {sl.dll_nxt == r2})
      (c  : t_of (vcell p r2) {(p.cell r2).get_ref c Backward == r1})
  : Lemma (sl `dll_snoc` c == sl `dll_append` dll_sglt c)
  = ()

#pop-options

(***** [dll_splitAt] *)

let dll_splitAt
      (n : nat)
      (#p : list_param) (#r0 : ref p.r) (#len : nat {n <= len}) (#r3 : ref p.r) (sl : dllist_sel_t p r0 len r3)
  : Tot (r1 : ref p.r & r2 : ref p.r & dllist_sel_t p r0 n r1 & dllist_sel_t p r2 (len-n) r3)
  =
    let r1 = if n = 0   then sl.dll_prv else (index sl.dll_sg (n-1))._1 in
    let r2 = if n = len then sl.dll_nxt else (index sl.dll_sg n)._1     in
    let sg0, sg1 = splitAt n sl.dll_sg in
    (**) Ll.splitAt_index n sl.dll_sg;
    (**) sg_exit_index r0 sl.dll_sg;
    (**) sg_exit_index sl.dll_prv sg0;
    (**) sg_exit_index r0 sg1;
    (**) sg_entry_index sg1 sl.dll_nxt;
    (|r1, r2,
      { dll_sg = sg0; dll_prv = sl.dll_prv; dll_nxt = r2 },
      { dll_sg = sg1; dll_prv = r1; dll_nxt = sl.dll_nxt } |)

let dll_splitAt_append
      (n : nat)
      (#p : list_param) (#r0 : ref p.r) (#len : nat {n <= len}) (#r3 : ref p.r) (sl : dllist_sel_t p r0 len r3)
  : Lemma (let (|r1, r2, sl0, sl1|) = dll_splitAt n sl in sl == dll_append sl0 sl1)
  = lemma_splitAt_append n sl.dll_sg

let dll_init_eq_splitAt
      (#p : list_param) (#r0 : ref p.r) (#len : nat {len > 0}) (#r2 : ref p.r) (sl : dllist_sel_t p r0 len r2)
  : Lemma (dll_init sl `dll_eq3` (dll_splitAt (len-1) sl)._3)
  =
    sg_exit_index r0 sl.dll_sg;
    sg_exit_index sl.dll_prv (init sl.dll_sg);
    Ll.unsnoc_eq_init sl.dll_sg

(***** [dll_mem] *)

let dll_mem
      (#p : list_param) (r : ref p.r) (#r0 : ref p.r) (#len : nat) (#r1 : ref p.r) (sl : dllist_sel_t p r0 len r1)
  : prop
  = memP r (map Mkdtuple2?._1 sl.dll_sg)

(***** [dll_remove] *)

let dll_remove
      (i : nat)
      (#p : list_param) (#r0 : ref p.r) (#len : nat {i < len}) (#r1 : ref p.r) (sl : dllist_sel_t p r0 len r1)
  : Tot (r0' : ref p.r & r1' : ref p.r & dllist_sel_t p r0' (len - 1) r1')
  =
    let (|rs0, rs1, sl0, sl1|) = dll_splitAt i sl in
    (| sg_entry (sl0.dll_sg @ tl sl1.dll_sg) sl1.dll_nxt, sg_exit sl0.dll_prv (sl0.dll_sg @ tl sl1.dll_sg),
    {
      dll_sg  = sl0.dll_sg @ tl sl1.dll_sg;
      dll_prv = sl0.dll_prv;
      dll_nxt = sl1.dll_nxt;
    }|)

let dll_remove_eq
      (i : nat)
      (#p : list_param) (#r0 : ref p.r) (#len : nat {i < len}) (#r1 : ref p.r) (sl : dllist_sel_t p r0 len r1)
  : Lemma (let (|r0', r1', sl'|)      = dll_remove i sl  in
           let (|rs0, rs1, sl0, sl1|) = dll_splitAt i sl in
           let sl1' = dll_tail sl1 in
           sl' `dll_eq3` (dll_append (dll_change_nxt sl0 (dll_entry sl1')) (dll_change_prv sl1' (dll_exit sl0))))
  =
    let (|rs0, rs1, sl0, sl1|) = dll_splitAt i sl in
    let sl1' = dll_tail sl1                       in
    dll_append_lem (dll_change_nxt sl0 (dll_entry sl1')) (dll_change_prv sl1' (dll_exit sl0))


(*** Ghost lemmas *)

val dllist_rew_len (#opened : Mem.inames) (p : list_param) (entry : ref p.r) (len0 len1 : nat) (exit : ref p.r)
  : SteelGhost unit opened
      (dllist p entry len0 exit) (fun () -> dllist p entry len1 exit)
      (requires fun _ -> len0 = len1)
      (ensures  fun h0 () h1 -> len0 = len1 /\ sel_dllist p entry len0 exit h0 == sel_dllist p entry len1 exit h1)

(***** Intro / Elim lemmas *)

val intro_dllist_nil (#opened : Mem.inames) (p : list_param) (entry : ref p.r) (exit : ref p.r)
  : SteelGhost unit opened
      emp (fun () -> dllist p entry 0 exit)
      (requires fun _ -> True)
      (ensures  fun _ () h1 -> sel_dllist p entry 0 exit h1 == dll_nil entry exit)
  
val elim_dllist_nil (#opened : Mem.inames) (p : list_param) (entry exit : ref p.r)
  : SteelGhost unit opened
      (dllist p entry 0 exit) (fun () -> emp)
      (requires fun _ -> True)
      (ensures  fun h0 () _ -> sel_dllist p entry 0 exit h0 == dll_nil entry exit)


val intro_dllist_cons (#opened : Mem.inames) (p : list_param) (r0 r1 : ref p.r) (len : nat) (r2 : ref p.r)
  : SteelGhost unit opened
      (vcell p r0 `star` dllist p r1 len r2) (fun () -> dllist p r0 (len+1) r2)
      (requires fun h0 ->
        g_cref p Forward r0 h0 == r1 /\
        (sel_dllist p r1 len r2 h0).dll_prv == r0)
      (ensures  fun h0 () h1 ->
        let c_0 = h0 (vcell p r0)           in
        let sl1 = sel_dllist p r1 len r2 h0 in
        (p.cell r0).get_ref c_0 Forward == r1 /\
        sl1.dll_prv == r0 /\
        sel_dllist p r0 (len+1) r2 h1 == dll_cons c_0 sl1)

val elim_dllist_cons (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len : nat) (r2 : ref p.r)
  : SteelGhost (G.erased (ref p.r)) opened
      (dllist p r0 (len+1) r2) (fun r1 -> vcell p r0 `star` dllist p r1 len r2)
      (requires fun _ -> True)
      (ensures  fun h0 r1 h1 ->
        let sl0 = sel_dllist p r0 (len+1) r2 h0 in
        let c_0 = h1 (vcell p r0)               in
        let sl1 = sel_dllist p r1 len r2 h1     in
        G.reveal r1 == dll_nxt0 sl0 /\
        (p.cell r0).get_ref c_0 Forward == G.reveal r1 /\ sl1.dll_prv == r0 /\
        sl0 == dll_cons c_0 sl1)


let intro_dllist_sglt (#opened : Mem.inames) (p : list_param) (r : ref p.r)
  : SteelGhost unit opened
      (vcell p r) (fun () -> dllist p r 1 r)
      (requires fun _ -> True)
      (ensures  fun h0 () h1 ->
        sel_dllist p r 1 r h1 == dll_sglt (h0 (vcell p r)))
  =
    let c   = gget (vcell p r)             in
    let nxt = (p.cell r).get_ref c Forward in
    intro_dllist_nil  p nxt r;
    intro_dllist_cons p r nxt 0 r

let elim_dllist_sglt_2 (#opened : Mem.inames) (p : list_param) (r0 r1 : ref p.r)
  : SteelGhost unit opened
      (dllist p r0 1 r1) (fun () -> vcell p r0)
      (requires fun _ -> True)
      (ensures  fun h0 () h1 ->
        r0 == r1 /\
        sel_dllist p r0 1 r1 h0 == dll_sglt (h1 (vcell p r0)))
  =
    let nxt = elim_dllist_cons p r0 0 r1 in
    elim_dllist_nil p nxt r1

let elim_dllist_sglt (#opened : Mem.inames) (p : list_param) (r : ref p.r)
  : SteelGhost unit opened
      (dllist p r 1 r) (fun () -> vcell p r)
      (requires fun _ -> True)
      (ensures  fun h0 () h1 ->
        sel_dllist p r 1 r h0 == dll_sglt (h1 (vcell p r)))
  = elim_dllist_sglt_2 p r r


(***** Append *)

val intro_dllist_append
      (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len0 : nat) (r1 r2 : ref p.r) (len1 : nat) (r3 : ref p.r)
  : SteelGhost unit opened
      (dllist p r0 len0 r1 `star` dllist p r2 len1 r3) (fun () -> dllist p r0 (len0+len1) r3)
      (requires fun h0 ->
         (sel_dllist p r0 len0 r1 h0).dll_nxt == r2 /\
         (sel_dllist p r2 len1 r3 h0).dll_prv == r1)
      (ensures  fun h0 () h1 ->
         let sl0 = sel_dllist p r0 len0 r1 h0 in
         let sl1 = sel_dllist p r2 len1 r3 h0 in
         sl0.dll_nxt == r2 /\ sl1.dll_prv == r1 /\
         sel_dllist p r0 (len0+len1) r3 h1 == dll_append sl0 sl1)

val elim_dllist_append
      (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len0 : nat) (r1 r2 : ref p.r) (len1 : nat) (r3 : ref p.r)
      (sl0 : dllist_sel_t p r0 len0 r1 {sl0.dll_nxt == r2})
      (sl1 : dllist_sel_t p r2 len1 r3 {sl1.dll_prv == r1})
  : SteelGhost unit opened
      (dllist p r0 (len0+len1) r3) (fun () -> dllist p r0 len0 r1 `star` dllist p r2 len1 r3)
      (requires fun h0 ->
         sel_dllist p r0 (len0+len1) r3 h0 == dll_append sl0 sl1)
      (ensures  fun h0 () h1 ->
         sel_dllist p r0 len0 r1 h1 == sl0 /\
         sel_dllist p r2 len1 r3 h1 == sl1)

val intro_dllist_snoc (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len : nat) (r1 r2 : ref p.r)
  : SteelGhost unit opened
      (dllist p r0 len r1 `star` vcell p r2) (fun () -> dllist p r0 (len+1) r2)
      (requires fun h0 ->
         (sel_dllist p r0 len r1 h0).dll_nxt == r2 /\
         g_cref p Backward r2 h0 == r1)
      (ensures  fun h0 () h1 ->
         let c   = h0 (vcell p r2)           in
         let sl0 = sel_dllist p r0 len r1 h0 in
         sl0.dll_nxt == r2 /\ (p.cell r2).get_ref c Backward == r1 /\
         sel_dllist p r0 (len+1) r2 h1 == sl0 `dll_snoc` c)

val elim_dllist_snoc (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len : nat) (r2 : ref p.r)
  : SteelGhost (G.erased (ref p.r)) opened
      (dllist p r0 (len+1) r2) (fun r1 -> dllist p r0 len r1 `star` vcell p r2)
      (requires fun _ -> True)
      (ensures  fun h0 r1 h1 ->
         let sl1 = sel_dllist p r0 (len+1) r2 h0 in
         let c   = h1 (vcell p r2)               in
         let sl0 = sel_dllist p r0 len r1 h1     in
         G.reveal r1 == dll_prv0 sl1 /\
         sl0.dll_nxt == r2 /\ (p.cell r2).get_ref c Backward == G.reveal r1 /\
         sl1 == sl0 `dll_snoc` c)

(***** Null *)

val dllist_entry_null_iff_lem (p : list_param) (r0 : ref p.r) (len : nat) (r1 : ref p.r) (m : Mem.mem)
  : Lemma (requires Mem.interp (hp_of (dllist p r0 len r1)) m /\
                    (sel_of (dllist p r0 len r1) m <: dllist_sel_t p r0 len r1).dll_nxt == null)
          (ensures  is_null r0 <==> len = 0)

val dllist_entry_null_iff (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len : nat) (r1 : ref p.r)
  : SteelGhost unit opened
      (dllist p r0 len r1) (fun () -> dllist p r0 len r1)
      (requires fun h0 ->
        (sel_dllist p r0 len r1 h0).dll_nxt == null)
      (ensures  fun h0 () h1 ->
        frame_equalities (dllist p r0 len r1) h0 h1 /\
        (is_null r0 <==> len = 0))

val dllist_exit_null_iff (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len : nat) (r1 : ref p.r)
  : SteelGhost unit opened
      (dllist p r0 len r1) (fun () -> dllist p r0 len r1)
      (requires fun h0 ->
        (sel_dllist p r0 len r1 h0).dll_prv == null)
      (ensures  fun h0 () h1 ->
        frame_equalities (dllist p r0 len r1) h0 h1 /\
        (is_null r1 <==> len = 0))


(*** Non-ghost operations *)

inline_for_extraction
val dllist_read_next
      (p : list_param) (r0 : ref p.r)
      (len : G.erased nat) (len' : G.erased nat {G.reveal len = len'+1}) (r2 : G.erased (ref p.r))
  : Steel (ref p.r)
      (dllist p r0 len r2) (fun r1 -> vcell p r0 `star` dllist p r1 len' r2)
      (requires fun _ -> True)
      (ensures  fun h0 r1 h1 ->
        let sl0 = sel_dllist p r0 len r2 h0  in
        let c_0 = h1 (vcell p r0)            in
        let sl1 = sel_dllist p r1 len' r2 h1 in
        r1 == dll_nxt0 sl0 /\
        (p.cell r0).get_ref c_0 Forward == r1 /\ sl1.dll_prv == r0 /\
        sl0 == dll_cons c_0 sl1)

// ALT? ghost version
inline_for_extraction
val dllist_splitOn
      (p : list_param) (r0 : ref p.r) (len : G.erased nat) (r1 : G.erased (ref p.r))
      (r : ref p.r) (i : G.erased (Fin.fin len))
  : Steel (ref p.r & ref p.r)
      (dllist p r0 len r1)
      (fun rs -> dllist p r0 i rs._1 `star` vcell p r `star` dllist p rs._2 (len-i-1) r1)
      (requires fun h0 ->
        (index (sel_dllist p r0 len r1 h0).dll_sg i)._1 == r)
      (ensures  fun h0 rs h1 ->
        let sl  = sel_dllist p   r0     len      r1    h0 in
        let sl0 = sel_dllist p   r0      i     rs._1   h1 in
        let sl1 = sel_dllist p rs._2 (len-i-1)   r1    h1 in
        let c : t_of (vcell p r) = SU.hsel (vcell p r) h1 in
        let sls = dll_splitAt i sl                        in
        sl0 `dll_eq3` sls._3 /\
        sl1 `dll_eq3` dll_tail sls._4 /\
        index sl.dll_sg i == (|r, (p.cell r).get_data c|) /\
        sl0.dll_nxt == r /\
        (p.cell r).get_ref c Backward == rs._1 /\
        (p.cell r).get_ref c Forward  == rs._2 /\
        sl1.dll_prv == r /\
        sl `dll_eq3` (sl0 `dll_append` (c `dll_cons` sl1)))

inline_for_extraction
val dllist_change_prv_cons
      (p : list_param) (r0 : ref p.r) (len : G.erased nat {len > 0}) (r1 : G.erased (ref p.r))
      (prv : ref p.r)
  : Steel unit
      (dllist p r0 len r1) (fun () -> dllist p r0 len r1)
      (requires fun _ -> True)
      (ensures  fun h0 () h1 ->
        sel_dllist p r0 len r1 h1 == dll_change_prv (sel_dllist p r0 len r1 h0) prv)

inline_for_extraction
val dllist_change_prv
      (p : list_param) (r0 : ref p.r) (len : G.erased nat) (r1 : G.erased (ref p.r))
      (prv : ref p.r)
  : Steel (G.erased (ref p.r))
      (dllist p r0 len r1) (fun r1' -> dllist p r0 len r1')
      (requires fun h0 ->
        (sel_dllist p r0 len r1 h0).dll_nxt == null)
      (ensures  fun h0 r1' h1 ->
        sel_dllist p r0 len r1' h1 `dll_eq3` dll_change_prv (sel_dllist p r0 len r1 h0) prv)

inline_for_extraction
val dllist_change_nxt_cons
      (p : list_param) (r0 : G.erased (ref p.r)) (len : G.erased nat {len > 0}) (r1 : ref p.r)
      (nxt : ref p.r)
  : Steel unit
      (dllist p r0 len r1) (fun () -> dllist p r0 len r1)
      (requires fun _ -> True)
      (ensures  fun h0 () h1 ->
        sel_dllist p r0 len r1 h1 == dll_change_nxt (sel_dllist p r0 len r1 h0) nxt)

/// Contrary to [dllist_change_prv] we return the bound that may have changed as a non-ghost variable.
/// For this we need [r0] to be non-ghost.
inline_for_extraction
val dllist_change_nxt
      (p : list_param) (r0 : ref p.r) (len : G.erased nat) (r1 : ref p.r)
      (nxt : ref p.r)
  : Steel (ref p.r)
      (dllist p r0 len r1) (fun r0' -> dllist p r0' len r1)
      (requires fun h0 ->
        (sel_dllist p r0 len r1 h0).dll_prv == null)
      (ensures  fun h0 r0' h1 ->
        sel_dllist p r0' len r1 h1 `dll_eq3` dll_change_nxt (sel_dllist p r0 len r1 h0) nxt)
