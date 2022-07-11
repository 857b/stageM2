module Learn.Steel.DLList.Derived

#set-options "--ifuel 1 --fuel 1"

(*** Operations on [dllist_sel_t] *)

let dll_tail_lem
      (#p : list_param) (#r0 : ref p.r) (#len : nat {len > 0}) (#r2 : ref p.r) (sl0 : dllist_sel_t p r0 len r2)
  : Lemma (sg_exit r0 (tl sl0.dll_sg) == r2)
  = ()

let dll_append_lem
      (#p : list_param) (#r0 : ref p.r) (#len0 : nat) (#r1 #r2 : ref p.r) (#len1 : nat) (#r3 : ref p.r)
      (sl0 : dllist_sel_t p r0 len0 r1 { sl0.dll_nxt == r2 })
      (sl1 : dllist_sel_t p r2 len1 r3 { sl1.dll_prv == r1 })
  : Lemma (sg_entry (sl0.dll_sg @ sl1.dll_sg) sl1.dll_nxt == r0 /\
           sg_exit  sl0.dll_prv (sl0.dll_sg @ sl1.dll_sg) == r3)
  = if Cons? (sl1.dll_sg) then lemma_append_last sl0.dll_sg sl1.dll_sg

#push-options "--ifuel 1 --fuel 2"
let dll_tail_append #p #r0 #len0 #r1 #r2 #len1 #r3 sl0 sl1 = ()
#pop-options

(*** Ghost lemmas *)

let dllist_rew_len (#opened : Mem.inames) (p : list_param) (entry : ref p.r) (len0 len1 : nat) (exit : ref p.r)
  =
    change_equal_slprop (dllist p entry len0 exit) (dllist p entry len1 exit)

(*****  Intro / Elim lemmas *)

let intro_dllist_nil (#opened : Mem.inames) (p : list_param) (entry exit : ref p.r)
  =
    change_slprop_rel emp (dllist p entry 0 exit)
      (fun _ sl -> sl == Mkdllist_sel_t [] exit entry)
      (fun m -> dllist_nil_interp p entry exit m)
  
let elim_dllist_nil (#opened : Mem.inames) (p : list_param) (entry exit : ref p.r)
  =
    change_slprop_rel (dllist p entry 0 exit) emp
      (fun sl _ -> sl == Mkdllist_sel_t [] exit entry)
      (fun m -> dllist_nil_interp p entry exit m; reveal_emp (); Mem.intro_emp m)


let intro_dllist_cons (#opened : Mem.inames) (p : list_param) (r0 r1 : ref p.r) (len : nat) (r2 : ref p.r)
  =
    let c0  = gget (vcell p r0)                    in
    let c_0 = (p.cell r0).cl_f c0                  in
    let sl1 = gget (dllist p r1 len r2)            in
    let sl0 = dll_cons #p #r0 #r1 #len #r2 c_0 sl1 in
    change_slprop (vcell p r0 `star` dllist p r1 len r2) (dllist p r0 (len+1) r2)
      (G.reveal c0, G.reveal sl1) sl0
      (fun m -> dllist_cons_interp p r0 len r2 m; dllist_cons_sel_eq p r0 len r2 m)

let elim_dllist_cons (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len : nat) (r2 : ref p.r)
  =
    let sl0 : G.erased (dllist_sel_t p r0 (len+1) r2) = gget (dllist p r0 (len+1) r2) in
    let hd :: tl = G.reveal sl0.dll_sg in
    let r1 : ref p.r = sg_entry tl sl0.dll_nxt in
    change_slprop_rel_with_cond
      (dllist p r0 (len+1) r2) (vcell p r0 `star` dllist p r1 len r2)
      (fun sl0' -> sl0' == G.reveal sl0)
      (fun _ (c0, sl1) ->
        let c_0 = (p.cell r0).cl_f c0            in
        let sl1 : dllist_sel_t p r1 len r2 = sl1 in
        c_0.cl_nxt == r1 /\ sl1.dll_prv == r0 /\
        G.reveal sl0 == dll_cons #p #r0 #r1 #len #r2 c_0 sl1)
      (fun m -> dllist_cons_interp p r0 len r2 m; dllist_cons_sel_eq p r0 len r2 m);
    r1


(***** Append *)

let rec intro_dllist_append
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
      (decreases len0)
  =
    if len0 = 0
    then begin
      dllist_rew_len p r0 len0 0 r1;
      elim_dllist_nil p r0 r1;
      change_equal_slprop (dllist p r2 len1 r3) (dllist p r0 (len0+len1) r3)
    end else begin
      let len0' = len0 - 1 in
      dllist_rew_len p r0 len0 (len0'+1) r1;
      let r0' = elim_dllist_cons p r0 len0' r1 in
      let c   = gget_cl p r0                   in
      let sl0 = gget (dllist p r0' len0' r1)   in
      let sl1 = gget (dllist p r2  len1  r3)   in
      intro_dllist_append p r0' len0' r1 r2 len1 r3;
      intro_dllist_cons p r0 r0' (len0'+len1) r3;
      dll_append_cons p r0 r0' len0' r1 r2 len1 r3 c sl0 sl1;
      dllist_rew_len p r0 ((len0'+len1)+1) (len0 + len1) r3
    end

let rec elim_dllist_append
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
      (decreases len0)
  =
    if len0 = 0
    then begin
      intro_dllist_nil p r0 r1;
      dllist_rew_len p r0 0 len0 r1;
      change_equal_slprop (dllist p r0 (len0+len1) r3) (dllist p r2 len1 r3)
    end else begin
      let len0' = len0 - 1 in
      dllist_rew_len p r0 (len0+len1) ((len0'+len1)+1) r3;
      let r0' : G.erased (ref p.r) = elim_dllist_cons p r0 (len0'+len1) r3 in
      let c0 = gget_cl p r0 in
      let sl' : G.erased (dllist_sel_t p r0' (len0'+len1) r3) = gget (dllist p r0' (len0'+len1) r3) in
      dll_tail_append sl0 sl1;
      let sl0' : dllist_sel_t p r0' len0' r1 = U.cast _ (dll_tail sl0) in
      assert (G.reveal sl' === dll_tail (dll_append sl0 sl1));
      assert (G.reveal sl' === dll_append sl0' sl1);
      elim_dllist_append p r0' len0' r1 r2 len1 r3 sl0' sl1;
      intro_dllist_cons p r0 r0' len0' r1;
      dllist_rew_len p r0 (len0'+1) len0 r1
    end


let intro_dllist_snoc (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len : nat) (r1 r2 : ref p.r)
  =
    intro_dllist_sglt p r2;
    intro_dllist_append p r0 len r1 r2 1 r2

let elim_dllist_snoc (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len : nat) (r2 : ref p.r)
  =
    let sl1 : G.erased (dllist_sel_t p r0 (len+1) r2) = gget (dllist p r0 (len+1) r2) in
    let (|r1, r2', sl0, slc|) = dll_splitAt len sl1 in
    dll_splitAt_append len sl1;
    dll_init_eq_splitAt sl1;
    let slc : dllist_sel_t p r2' 1 r2 = U.cast _ slc in
    elim_dllist_append p r0 len r1 r2' 1 r2 sl0 slc;
    elim_dllist_sglt_2 p r2' r2;
    change_equal_slprop (vcell p r2') (vcell p r2);
    noop ();
    r1

(***** Null *)

let dllist_entry_null_iff_lem (p : list_param) (r0 : ref p.r) (len : nat) (r1 : ref p.r) (m : Mem.mem)
  =
    if len > 0
    then begin
      dllist_cons_interp p r0 (len-1) r1 m;
      p.nnull r0 m
    end

let dllist_entry_null_iff (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len : nat) (r1 : ref p.r)
  =
    let sl0 = gget (dllist p r0 len r1) in
    extract_info (dllist p r0 len r1) sl0 (is_null r0 <==> len = 0)
      (dllist_entry_null_iff_lem p r0 len r1)

let dllist_exit_null_iff (#opened : Mem.inames) (p : list_param) (r0 : ref p.r) (len : nat) (r1 : ref p.r)
  =
    let sl0 = gget (dllist p r0 len r1) in
    if len > 0
    then begin
      let len' = len - 1 in
      dllist_rew_len p r0 len (len' + 1) r1;
      let r1' = elim_dllist_snoc p r0 len' r1 in
      list_cell_not_null p r1;
      intro_dllist_snoc p r0 len' r1' r1;
      dllist_rew_len p r0 (len' + 1) len r1
    end else noop ();
    let sl1 = gget (dllist p r0 len r1) in
    assert (sl0 == sl1)

(*** Non-ghost operations *)

inline_for_extraction
let dllist_read_next
      (p : list_param) (r0 : ref p.r)
      (len : G.erased nat) (len' : G.erased nat {G.reveal len = len'+1}) (r2 : G.erased (ref p.r))
  =
    (**) dllist_rew_len p r0 len (len'+1) r2;
    (**) let g_r1 : G.erased (ref p.r) = elim_dllist_cons p r0 len' r2 in
    let r1 : ref p.r = (p.cell r0).read_nxt () in
    (**) assert (G.reveal g_r1 == r1);
    (**) change_equal_slprop (dllist p g_r1 len' r2)
    (**)                     (dllist p r1   len' r2);
    return r1


#push-options "--z3rlimit 30 --ifuel 0"
inline_for_extraction
let dllist_splitOn
      (p : list_param) (r0 : ref p.r) (len : G.erased nat) (r1 : G.erased (ref p.r))
      (r : ref p.r) (i : G.erased (Fin.fin len))
  =
    (**) let sl    : G.erased (dllist_sel_t p r0 len r1) = gget (dllist p r0 len r1) in
    (**) let len1  : G.erased nat = G.hide (len-i)        in
    (**) let sls 
    (**)   : G.erased (rs0 : ref p.r & rs1 : ref p.r & dllist_sel_t p r0 i rs0 & dllist_sel_t p rs1 len1 r1)
    (**)   = G.hide (dll_splitAt i sl)                  in
    (**) let g_rs0 : G.erased (ref p.r) = G.hide sls._1 in
    (**) assert (sls._2 == r);
    (**) let sl0   : G.erased (dllist_sel_t p r0 i g_rs0) = G.hide sls._3 in
    (**) let sl1   : G.erased (dllist_sel_t p r len1 r1)  = G.hide sls._4 in
    (**) dll_splitAt_append i sl;
    (**) change_equal_slprop (dllist p r0   len    r1)
    (**)                     (dllist p r0 (i+len1) r1);
    (**) elim_dllist_append p r0 i g_rs0 r len1 r1 sl0 sl1;
    (**) let len2 : G.erased nat = G.hide (len1-1)       in
    let rs1 = dllist_read_next p r len1 len2 r1   in
    let rs0 = (p.cell r).read_prv ()              in
    (**) change_equal_slprop (dllist p r0 i g_rs0)
    (**)                     (dllist p r0 i   rs0);
    (**) let c    = gget_cl p r                        in
    (**) let sl1' : G.erased (dllist_sel_t p rs1 len2 r1) = gget (dllist p rs1 len2 r1) in
    (**) assert (G.reveal sl1 == dll_cons c sl1');
    (**) assert (dll_tail sl1 == G.reveal sl1');
    (**) U.assert_by (index sl.dll_sg i == (|r, c.cl_data|)) (fun () ->
    (**)   calc (==) {
    (**)     index sl.dll_sg i;
    (**)   == { Ll.splitAt_index i sl.dll_sg }
    (**)     index sl1.dll_sg 0;
    (**)   == { }
    (**)     index (dll_cons c sl1').dll_sg 0;
    (**)   == { U.by_refl () }
    (**)     (|r, c.cl_data|);
    (**)   }
    (**) );
    return (rs0, rs1)
#pop-options


inline_for_extraction
let dllist_change_prv_cons
      (p : list_param) (r0 : ref p.r) (len : G.erased nat {len > 0}) (r1 : G.erased (ref p.r))
      (prv : ref p.r)
  =
    (**) let len' = G.hide (len - 1)             in
    (**) dllist_rew_len p r0 len (len'+1) r1;
    (**) let r0' = elim_dllist_cons p r0 len' r1 in
    (p.cell r0).write_prv prv;
    (**) intro_dllist_cons p r0 r0' len' r1;
    (**) dllist_rew_len p r0 (len'+1) len r1

inline_for_extraction
let dllist_change_prv
      (p : list_param) (r0 : ref p.r) (len : G.erased nat) (r1 : G.erased (ref p.r))
      (prv : ref p.r)
  =
    (**) dllist_entry_null_iff p r0 len r1;
    if not (is_null r0)
    then begin
      dllist_change_prv_cons p r0 len r1 prv;
      (**) r1
    end else begin
      (**) dllist_rew_len p r0 len 0 r1;
      (**) elim_dllist_nil p r0 r1;
      (**) intro_dllist_nil p r0 prv;
      (**) dllist_rew_len p r0 0 len prv;
      (**) prv
    end

inline_for_extraction
let dllist_change_nxt_cons
      (p : list_param) (r0 : G.erased (ref p.r)) (len : G.erased nat {len > 0}) (r1 : ref p.r)
      (nxt : ref p.r)
  =
    (**) let len' = G.hide (len - 1)             in
    (**) dllist_rew_len p r0 len (len'+1) r1;
    (**) let r1' = elim_dllist_snoc p r0 len' r1 in
    (p.cell r1).write_nxt nxt;
    (**) intro_dllist_snoc p r0 len' r1' r1;
    (**) dllist_rew_len p r0 (len'+1) len r1

inline_for_extraction
let dllist_change_nxt
      (p : list_param) (r0 : ref p.r) (len : G.erased nat) (r1 : ref p.r)
      (nxt : ref p.r)
  =
    (**) dllist_exit_null_iff p r0 len r1;
    if is_null r1
    then begin
      (**) dllist_rew_len p r0 len 0 r1;
      (**) elim_dllist_nil p r0 r1;
      (**) intro_dllist_nil p nxt r1;
      (**) dllist_rew_len p nxt 0 len r1;
      return nxt
    end else begin
      dllist_change_nxt_cons p r0 len r1 nxt;
      r0
    end
