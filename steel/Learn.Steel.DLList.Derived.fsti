module Learn.Steel.DLList.Derived

module U   = Learn.Util
module G   = FStar.Ghost
module Ll  = Learn.List
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

let dll_hd (#p : list_param) (#r0 : ref p.r) (#len : nat) (#r1 : ref p.r) (sl : dllist_sel_t p r0 len r1)
  : ref p.r
  = r0

let dll_lt (#p : list_param) (#r0 : ref p.r) (#len : nat) (#r1 : ref p.r) (sl : dllist_sel_t p r0 len r1)
  : ref p.r
  = r1


unfold
let cl_eq3 #p #r (c : cell_t p r) #r' (c' : cell_t p r')
  : prop
  = r == r' /\ c == c'

unfold
let dll_eq3 #p #r0 #len #r1 (sl : dllist_sel_t p r0 len r1) #r0' #len' #r1' (sl' : dllist_sel_t p r0' len' r1')
  : prop
  = r0 == r0' /\ len == len' /\ r1 == r1' /\ sl == sl'


let sg_hd_index (#p : list_param) (l : list (rcell_t p)) (nxt : ref p.r)
  : Lemma (sg_hd l nxt == (if length l > 0 then (index l 0)._1 else nxt))
  = ()

let sg_lt_index (#p : list_param) (prv : ref p.r) (l : list (rcell_t p))
  : Lemma (sg_lt prv l == (if length l > 0 then (index l (length l - 1))._1 else prv))
  = if Cons? l then Ll.last_index l


let dll_change_nxt #p #r0 #len #r1 (sl : dllist_sel_t p r0 len r1) (nxt : ref p.r)
  : dllist_sel_t p (sg_hd sl.dll_sg nxt) len r1
  = {sl with dll_nxt = nxt}

let dll_change_prv #p #r0 #len #r1 (sl : dllist_sel_t p r0 len r1) (prv : ref p.r)
  : dllist_sel_t p r0 len (sg_lt prv sl.dll_sg)
  = {sl with dll_prv = prv}

let dll_next_at #p #r0 #len #r1 (sl : dllist_sel_t p r0 len r1) (i : nat {i <= len})
  : ref p.r
  = if i = len then sl.dll_nxt else (index sl.dll_sg   i  )._1

let dll_prev_at #p #r0 #len #r1 (sl : dllist_sel_t p r0 len r1) (i : nat {i <= len})
  : ref p.r
  = if i =  0  then sl.dll_prv else (index sl.dll_sg (i-1))._1

let dll_cell_at #p #r0 #len #r1 (sl : dllist_sel_t p r0 len r1) (i : Fin.fin len)
  : cell_t p (index sl.dll_sg i)._1
  = {
    cl_prv  = dll_prev_at sl i;
    cl_nxt  = dll_next_at sl (i+1);
    cl_data = (index sl.dll_sg i)._2;
  }


(***** [dll_head], [dll_tail] *)

let dll_nxt0 (#p : list_param) (#r0 : ref p.r) (#len : nat {len > 0}) (#r2 : ref p.r) (sl0 : dllist_sel_t p r0 len r2)
  : ref p.r
  = sg_hd (tl sl0.dll_sg) sl0.dll_nxt

#push-options "--fuel 2"
let dll_nxt0_eq #p #r0 (#len : nat {len > 0}) #r2 (sl : dllist_sel_t p r0 len r2)
  : Lemma (dll_nxt0 sl == dll_next_at sl 1)
  = if len > 1 then sg_hd_index (tl sl.dll_sg) sl.dll_nxt
#pop-options

let dll_head #p #r0 (#len : nat {len > 0}) #r2 (sl : dllist_sel_t p r0 len r2)
  : cell_t p r0
  = {
    cl_prv  = sl.dll_prv;
    cl_nxt  = dll_nxt0 sl;
    cl_data = (hd sl.dll_sg)._2;
  }

val dll_tail_lem
      (#p : list_param) (#r0 : ref p.r) (#len : nat {len > 0}) (#r2 : ref p.r) (sl0 : dllist_sel_t p r0 len r2)
  : Lemma (sg_lt r0 (tl sl0.dll_sg) == r2)

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
      (c  : cell_t p r0)
      (sl1 : dllist_sel_t p r1 len' r2 {sl1.dll_prv == r0})
  : Lemma (dll_tail (dll_cons c sl1) == sl1) [SMTPat (dll_tail (dll_cons c sl1))]
  = ()


(***** [dll_snoc] *)

let dll_snoc
      (#p : list_param) (#r0 : ref p.r) (#len : nat) (#r1 #r2 : ref p.r)
      (sl : dllist_sel_t p r0 len r1 {sl.dll_nxt == r2})
      (c  : cell_t p r2)
  : GTot (dllist_sel_t p r0 (len + 1) r2)
  =
    let sg_c = (|r2, c.cl_data|) in
    (**) lemma_append_last sl.dll_sg [sg_c];
    (**) assert_norm (length [sg_c] == 1);
    {
      dll_sg  = snoc (sl.dll_sg, sg_c);
      dll_prv = sl.dll_prv;
      dll_nxt = c.cl_nxt;
    }


(***** [dll_init] *)

let dll_prv0 (#p : list_param) (#r0 : ref p.r) (#len : nat {len > 0}) (#r2 : ref p.r) (sl : dllist_sel_t p r0 len r2)
  : ref p.r
  = sg_lt sl.dll_prv (init sl.dll_sg)

#push-options "--fuel 2"
let dll_prv0_eq #p #r0 (#len : nat {len > 0}) #r2 (sl : dllist_sel_t p r0 len r2)
  : Lemma (dll_prv0 sl == dll_prev_at sl (len - 1))
  =
    if len > 1
    then begin
      sg_lt_index sl.dll_prv (init sl.dll_sg);
      Ll.unsnoc_eq_init sl.dll_sg;
      lemma_unsnoc_index sl.dll_sg (len - 2)
    end
#pop-options

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
      (c  : cell_t p r2)
  : Lemma (dll_prv0 (dll_snoc sl c) == r1 /\ dll_init (dll_snoc sl c) == sl)
  =
    let sg_c = (|r2, c.cl_data|) in
    Ll.unsnoc_eq_init (snoc (sl.dll_sg, sg_c))


(***** [dll_append] *)


val dll_append_lem
      (#p : list_param) (#r0 : ref p.r) (#len0 : nat) (#r1 #r2 : ref p.r) (#len1 : nat) (#r3 : ref p.r)
      (sl0 : dllist_sel_t p r0 len0 r1 { sl0.dll_nxt == r2 })
      (sl1 : dllist_sel_t p r2 len1 r3 { sl1.dll_prv == r1 })
  : Lemma (sg_hd (sl0.dll_sg @ sl1.dll_sg) sl1.dll_nxt == r0 /\
           sg_lt  sl0.dll_prv (sl0.dll_sg @ sl1.dll_sg) == r3)

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
      (c   : cell_t p r0)
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

let dll_sglt (#p : list_param) (#r : ref p.r) (c : cell_t p r)
  : GTot (dllist_sel_t p r 1 r)
  = {
    dll_sg  = [(|r, c.cl_data|)];
    dll_prv = c.cl_prv;
    dll_nxt = c.cl_nxt;
  }

let dll_cons_as_append
      (#p : list_param) (#r0 #r1 : ref p.r) (#len' : nat) (#r2 : ref p.r)
      (c : cell_t p r0 {c.cl_nxt == r1})
      (sl : dllist_sel_t p r1 len' r2 {sl.dll_prv == r0})
  : Lemma (c `dll_cons` sl == dll_sglt c `dll_append` sl)
  = ()

let dll_snoc_as_append
      (#p : list_param) (#r0 : ref p.r) (#len : nat) (#r1 #r2 : ref p.r)
      (sl : dllist_sel_t p r0 len r1 {sl.dll_nxt == r2})
      (c  : cell_t p r2 {c.cl_prv == r1})
  : Lemma (sl `dll_snoc` c == sl `dll_append` dll_sglt c)
  = ()

#pop-options

(***** [dll_splitAt] *)

let dll_splitAt
      (n : nat)
      (#p : list_param) (#r0 : ref p.r) (#len : nat {n <= len}) (#r3 : ref p.r) (sl : dllist_sel_t p r0 len r3)
  : Tot (dllist_sel_t p r0 n (dll_prev_at sl n) & dllist_sel_t p (dll_next_at sl n) (len-n) r3)
  =
    let r1 = dll_prev_at sl n in
    let r2 = dll_next_at sl n in
    let sg0, sg1 = splitAt n sl.dll_sg in
    (**) Ll.splitAt_index n sl.dll_sg;
    (**) sg_lt_index r0 sl.dll_sg;
    (**) sg_lt_index sl.dll_prv sg0;
    (**) sg_lt_index r0 sg1;
    (**) sg_hd_index sg1 sl.dll_nxt;
    ({ dll_sg = sg0; dll_prv = sl.dll_prv; dll_nxt = r2 },
     { dll_sg = sg1; dll_prv = r1; dll_nxt = sl.dll_nxt })

let dll_splitAt_append
      (n : nat)
      (#p : list_param) (#r0 : ref p.r) (#len : nat {n <= len}) (#r3 : ref p.r) (sl : dllist_sel_t p r0 len r3)
  : Lemma (let (sl0, sl1) = dll_splitAt n sl in sl == dll_append sl0 sl1)
  = lemma_splitAt_append n sl.dll_sg

let dll_init_eq_splitAt
      (#p : list_param) (#r0 : ref p.r) (#len : nat {len > 0}) (#r2 : ref p.r) (sl : dllist_sel_t p r0 len r2)
  : Lemma (dll_init sl `dll_eq3` (dll_splitAt (len-1) sl)._1)
  =
    sg_lt_index r0 sl.dll_sg;
    Ll.unsnoc_eq_init sl.dll_sg;
    dll_prv0_eq sl

let dll_splitOn
      #p #r0 #len #r4 (sl : dllist_sel_t p r0 len r4) (i : Fin.fin len)
  : Tot (dllist_sel_t p r0 i (dll_prev_at sl i) &
         cell_t p (index sl.dll_sg i)._1 &
         dllist_sel_t p (dll_next_at sl (i+1)) (len-i-1) r4)
  = (dll_splitAt i sl)._1, dll_cell_at sl i, (dll_splitAt (i+1) sl)._2

val dll_splitOn_eq
      (#p : list_param) (#r0 : ref p.r) (#len : nat) (#r4 : ref p.r) (sl : dllist_sel_t p r0 len r4)
      (i : Fin.fin len)
  : Lemma (let sls = dll_splitAt i sl in
           dll_next_at sl (i+1) == dll_nxt0 sls._2 /\
           dll_splitOn sl i == (sls._1, dll_head sls._2, dll_tail sls._2))


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
    let sl0, _, sl1 = dll_splitOn sl i in
    (| sg_hd (sl0.dll_sg @ sl1.dll_sg)  sl1.dll_nxt,
       sg_lt  sl0.dll_prv (sl0.dll_sg @ sl1.dll_sg),
    {
      dll_sg  = sl0.dll_sg @ sl1.dll_sg;
      dll_prv = sl0.dll_prv;
      dll_nxt = sl1.dll_nxt;
    }|)

let dll_remove_eq
      (i : nat)
      (#p : list_param) (#r0 : ref p.r) (#len : nat {i < len}) (#r1 : ref p.r) (sl : dllist_sel_t p r0 len r1)
  : Lemma (let (|r0', r1', sl'|) = dll_remove i sl  in
           let sl0, _, sl1       = dll_splitOn sl i in
           sl' `dll_eq3` (dll_append (dll_change_nxt sl0 (dll_hd sl1)) (dll_change_prv sl1 (dll_lt sl0))))
  =
    let sl0, _, sl1 = dll_splitOn sl i in
    dll_append_lem (dll_change_nxt sl0 (dll_hd sl1)) (dll_change_prv sl1 (dll_lt sl0))


(*** Ghost lemmas *)

val dllist_rew_len (#opened : Mem.inames) (p : list_param) (hd : ref p.r) (len0 len1 : nat) (lt : ref p.r)
  : SteelGhost unit opened
      (dllist p hd len0 lt) (fun () -> dllist p hd len1 lt)
      (requires fun _ -> len0 = len1)
      (ensures  fun h0 () h1 -> len0 = len1 /\ sel_dllist p hd len0 lt h0 == sel_dllist p hd len1 lt h1)

(***** Intro / Elim lemmas *)

val intro_dllist_nil (#opened : Mem.inames) (p : list_param) (hd : ref p.r) (lt : ref p.r)
  : SteelGhost unit opened
      emp (fun () -> dllist p hd 0 lt)
      (requires fun _ -> True)
      (ensures  fun _ () h1 -> sel_dllist p hd 0 lt h1 == dll_nil hd lt)
  
val elim_dllist_nil (#opened : Mem.inames) (p : list_param) (hd lt : ref p.r)
  : SteelGhost unit opened
      (dllist p hd 0 lt) (fun () -> emp)
      (requires fun _ -> True)
      (ensures  fun h0 () _ -> sel_dllist p hd 0 lt h0 == dll_nil hd lt)


val intro_dllist_cons (#opened : Mem.inames) (p : list_param) (r0 r1 : ref p.r) (len : nat) (r2 : ref p.r)
  : SteelGhost unit opened
      (vcell p r0 `star` dllist p r1 len r2) (fun () -> dllist p r0 (len+1) r2)
      (requires fun h0 ->
        (g_cl p r0 h0).cl_nxt == r1 /\
        (sel_dllist p r1 len r2 h0).dll_prv == r0)
      (ensures  fun h0 () h1 ->
        let c_0 = g_cl p r0 h0              in
        let sl1 = sel_dllist p r1 len r2 h0 in
        c_0.cl_nxt  == r1 /\
        sl1.dll_prv == r0 /\
        sel_dllist p r0 (len+1) r2 h1 == dll_cons c_0 sl1)

val elim_dllist_cons (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len : nat) (r2 : ref p.r)
  : SteelGhost (G.erased (ref p.r)) opened
      (dllist p r0 (len+1) r2) (fun r1 -> vcell p r0 `star` dllist p r1 len r2)
      (requires fun _ -> True)
      (ensures  fun h0 r1 h1 ->
        let sl0 = sel_dllist p r0 (len+1) r2 h0 in
        let c_0 = g_cl p r0 h1                  in
        let sl1 = sel_dllist p r1 len r2 h1     in
        G.reveal r1 == dll_nxt0 sl0 /\
        c_0.cl_nxt == G.reveal r1 /\ sl1.dll_prv == r0 /\
        sl0 == dll_cons c_0 sl1)


let intro_dllist_sglt (#opened : Mem.inames) (p : list_param) (r : ref p.r)
  : SteelGhost unit opened
      (vcell p r) (fun () -> dllist p r 1 r)
      (requires fun _ -> True)
      (ensures  fun h0 () h1 ->
        sel_dllist p r 1 r h1 == dll_sglt (g_cl p r h0))
  =
    let c   = gget_cl p r in
    let nxt = c.cl_nxt    in
    intro_dllist_nil  p nxt r;
    intro_dllist_cons p r nxt 0 r

let elim_dllist_sglt_2 (#opened : Mem.inames) (p : list_param) (r0 r1 : ref p.r)
  : SteelGhost unit opened
      (dllist p r0 1 r1) (fun () -> vcell p r0)
      (requires fun _ -> True)
      (ensures  fun h0 () h1 ->
        r0 == r1 /\
        sel_dllist p r0 1 r1 h0 == dll_sglt (g_cl p r0 h1))
  =
    let nxt = elim_dllist_cons p r0 0 r1 in
    elim_dllist_nil p nxt r1

let elim_dllist_sglt (#opened : Mem.inames) (p : list_param) (r : ref p.r)
  : SteelGhost unit opened
      (dllist p r 1 r) (fun () -> vcell p r)
      (requires fun _ -> True)
      (ensures  fun h0 () h1 -> sel_dllist p r 1 r h0 == dll_sglt (g_cl p r h1))
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
         (g_cl p r2 h0).cl_prv == r1)
      (ensures  fun h0 () h1 ->
         let c   = g_cl p r2 h0              in
         let sl0 = sel_dllist p r0 len r1 h0 in
         sl0.dll_nxt == r2 /\ c.cl_prv == r1 /\
         sel_dllist p r0 (len+1) r2 h1 == sl0 `dll_snoc` c)

val elim_dllist_snoc (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len : nat) (r2 : ref p.r)
  : SteelGhost (G.erased (ref p.r)) opened
      (dllist p r0 (len+1) r2) (fun r1 -> dllist p r0 len r1 `star` vcell p r2)
      (requires fun _ -> True)
      (ensures  fun h0 r1 h1 ->
         let sl1 = sel_dllist p r0 (len+1) r2 h0 in
         let c   = g_cl p r2 h1                  in
         let sl0 = sel_dllist p r0 len r1 h1     in
         G.reveal r1 == dll_prv0 sl1 /\
         sl0.dll_nxt == r2 /\ c.cl_prv == G.reveal r1 /\
         sl1 == sl0 `dll_snoc` c)

val dllist_splitOn
      (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len : nat) (r1 : ref p.r)
      (r : ref p.r) (i : Fin.fin len)
  : SteelGhost (G.erased (ref p.r & ref p.r)) opened
      (dllist p r0 len r1)
      (fun rs -> dllist p r0 i (fst rs) `star` vcell p r `star` dllist p (snd rs) (len-i-1) r1)
      (requires fun h0 ->
        (index (sel_dllist p r0 len r1 h0).dll_sg i)._1 == r)
      (ensures  fun h0 rs h1 ->
        let sl  = sel_dllist p    r0       len       r1    h0 in
        let sl0 = sel_dllist p    r0        i     (fst rs) h1 in
        let sl1 = sel_dllist p (snd rs) (len-i-1)    r1    h1 in
        let c : cell_t p r = g_cl p r h1                      in
        let sls = dll_splitOn sl i                            in
        sl0 `dll_eq3` sls._1  /\  c `cl_eq3` sls._2  /\  sl1 `dll_eq3` sls._3 /\
        sl `dll_eq3` (sl0 `dll_append` (c `dll_cons` sl1)))


(***** Null *)

val dllist_hd_null_iff_lem (p : list_param) (r0 : ref p.r) (len : nat) (r1 : ref p.r) (m : Mem.mem)
  : Lemma (requires Mem.interp (hp_of (dllist p r0 len r1)) m /\
                    (sel_of (dllist p r0 len r1) m <: dllist_sel_t p r0 len r1).dll_nxt == null)
          (ensures  is_null r0 <==> len = 0)

val dllist_hd_null_iff (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len : nat) (r1 : ref p.r)
  : SteelGhost unit opened
      (dllist p r0 len r1) (fun () -> dllist p r0 len r1)
      (requires fun h0 ->
        (sel_dllist p r0 len r1 h0).dll_nxt == null)
      (ensures  fun h0 () h1 ->
        frame_equalities (dllist p r0 len r1) h0 h1 /\
        (is_null r0 <==> len = 0))

val dllist_lt_null_iff (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len : nat) (r1 : ref p.r)
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
        let c_0 = g_cl p r0 h1               in
        let sl1 = sel_dllist p r1 len' r2 h1 in
        r1 == dll_nxt0 sl0 /\
        c_0.cl_nxt == r1 /\ sl1.dll_prv == r0 /\
        sl0 == dll_cons c_0 sl1)

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
