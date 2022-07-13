module Experiment.Steel.VEquiv

module T = FStar.Tactics

open FStar.List.Pure
open Learn.List.Mask

#push-options "--ifuel 1 --fuel 2"

let rec veq_sel_eq_eff_aux_sound
      (#pre #post : Fl.ty_list) (f_eq : veq_eq_t (length pre) (length post))
      (sl0 : Fl.flist pre) (sl1 : Fl.flist post) (i : nat)
  : Lemma (requires veq_typ_eq pre post f_eq)
          (ensures  veq_sel_eq_eff_aux f_eq sl0 sl1 i <==>
                   (forall (j : Fin.fin (length post) {Some? (f_eq j)}) . i <= j ==> sl1 j === sl0 (Some?.v (f_eq j))))
          (decreases length post - i)
  = if i < length post then veq_sel_eq_eff_aux_sound f_eq sl0 sl1 (i+1)

let veq_sel_eq_eff_sound
      (#pre #post : Fl.ty_list) (f_eq : veq_eq_t (length pre) (length post))
      (sl0 : Fl.flist pre) (sl1 : Fl.flist post)
  : Lemma (requires veq_typ_eq pre post f_eq)
          (ensures  veq_sel_eq_eff f_eq sl0 sl1 <==> veq_sel_eq f_eq sl0 sl1)
          [SMTPat (veq_sel_eq_eff f_eq sl0 sl1)]
  = veq_sel_eq_eff_aux_sound f_eq sl0 sl1 0

#push-options "--z3rlimit 10"
let veq_sel_eq_iff_partial_eq
      (#pre #post : Fl.ty_list) (l_eq : veq_eq_t_list (length pre) (length post))
      (sl0 : Fl.flist pre) (sl1 : Fl.flist post)
  = ()
#pop-options


let vequiv_refl_sel_eq
      (#v: vprop_list) (sl0 : sl_f v) (sl1 : sl_f v)
  : squash (veq_sel_eq (veq_eq_sl (veq_of_list (vequiv_refl_eq v))) sl0 sl1 <==> sl1 == sl0)
  = introduce _ /\  _
       with introduce _ ==> _ with _ .
            Fl.flist_extensionality sl1 sl0 (fun i -> ())
        and ()

(***** [vequiv_trans] *)

let vequiv_trans_eq1_restr_typ (#v0 #v1 #v2 : vprop_list) (e0 : vequiv v0 v1) (e1 : vequiv v1 v2)
  : Lemma (requires veq_typ_eq (vprop_list_sels_t v1) (vprop_list_sels_t v2) (veq_eq_sl (veq_f e1)))
          (ensures  veq_typ_eq (vprop_list_sels_t v1) (vprop_list_sels_t v2)
                          (veq_eq_sl (veq_of_list (vequiv_trans_eq1_restr e0 e1))))
  =
    let f_eq = veq_eq_sl (veq_of_list (vequiv_trans_eq1_restr e0 e1)) in
    introduce forall (i : Fin.fin (length v2) {Some? (f_eq i)}) .
                  (index v2 i).t == (index v1 (Some?.v (f_eq i))).t
      with assert (f_eq i == vequiv_trans_eq1_restr_f e0 (index e1.veq_eq i))

let vequiv_trans_req_iff (#v0 #v1 #v2 : vprop_list) (e0 : vequiv v0 v1) (e1 : vequiv v1 v2)
                         (sl0 : sl_f v0)
  : Lemma (vequiv_trans_req e0 e1 sl0 <==>
            (e0.veq_req sl0 /\ (forall (sl1 : sl_f v1) . veq_ens1 e0 sl0 sl1 ==> e1.veq_req sl1)))
  =
    let p_eq = veq_partial_eq e0.veq_eq sl0 in
    let p (sl1 : sl_f v1) = e0.veq_ens sl0 sl1 ==> e1.veq_req sl1 in
    calc (<==>) {
      vequiv_trans_req e0 e1 sl0;
    <==> { assert (vequiv_trans_req e0 e1 sl0 == (e0.veq_req sl0 /\ Fl.forall_flist_part _ p_eq p))
             by (T.trefl ()) }
      e0.veq_req sl0 /\ Fl.forall_flist_part _ p_eq p;
    <==> { Fl.forall_flist_part_iff _ p_eq p }
      e0.veq_req sl0 /\ (forall (sl1 : sl_f v1 {Fl.partial_eq sl1 p_eq}) . p sl1);
    <==> { FStar.Classical.forall_intro (FStar.Classical.move_requires
           (veq_sel_eq_iff_partial_eq #(vprop_list_sels_t v0) #(vprop_list_sels_t v1) e0.veq_eq sl0)) }
      e0.veq_req sl0 /\ (forall (sl1 : sl_f v1 {veq_sel_eq (veq_eq_sl (veq_of_list e0.veq_eq)) sl0 sl1}) . p sl1);
    <==> { }
      e0.veq_req sl0 /\ (forall (sl1 : sl_f v1) . veq_ens1 e0 sl0 sl1 ==> e1.veq_req sl1);
    }

let vequiv_trans_ens_imp (#v0 #v1 #v2 : vprop_list) (e0 : vequiv v0 v1) (e1 : vequiv v1 v2)
                         (sl0 : sl_f v0) (sl2 : sl_f v2)
  : Lemma ((exists (sl1 : sl_f v1) . veq_ens1 e0 sl0 sl1 /\ veq_ens1 e1 sl1 sl2)
            ==> vequiv_trans_ens e0 e1 sl0 sl2)
  =
    e1.veq_typ;
    vequiv_trans_eq1_restr_typ e0 e1;
    let f_eq = veq_eq_sl (veq_of_list (vequiv_trans_eq1_restr e0 e1)) in
    let p_eq = veq_partial_eq e0.veq_eq sl0                           in
    let p1 (sl1 : sl_f v1) = e1.veq_ens sl1 sl2                       in
    let p2 (sl1 : sl_f v1) = veq_sel_eq_eff f_eq sl1 sl2              in
    let p  (sl1 : sl_f v1) = e0.veq_ens sl0 sl1 /\ p1 sl1 /\ p2 sl1    in
    calc (<==>) {
      vequiv_trans_ens e0 e1 sl0 sl2;
    <==> { assert (vequiv_trans_ens e0 e1 sl0 sl2 == Fl.exists_flist_part _ p_eq p)
             by (T.trefl ()) }
      Fl.exists_flist_part _ p_eq p;
    <==> { Fl.exists_flist_part_iff _ p_eq p }
      exists (sl1 : sl_f v1 {Fl.partial_eq sl1 p_eq}) . p sl1;
    <==> { FStar.Classical.forall_intro (FStar.Classical.move_requires
           (veq_sel_eq_iff_partial_eq #(vprop_list_sels_t v0) #(vprop_list_sels_t v1) e0.veq_eq sl0)) }
      exists (sl1 : sl_f v1) . (veq_sel_eq (veq_eq_sl (veq_of_list e0.veq_eq)) sl0 sl1 /\ p sl1);
    <==> { }
      exists (sl1 : sl_f v1) . veq_ens1 e0 sl0 sl1 /\ p1 sl1 /\ p2 sl1;
    <==> { }
      exists (sl1 : sl_f v1) . veq_ens1 e0 sl0 sl1 /\ e1.veq_ens sl1 sl2 /\ veq_sel_eq f_eq sl1 sl2;
    };
    introduce forall (sl1 : sl_f v1 { veq_ens1 e1 sl1 sl2 }) . veq_sel_eq f_eq sl1 sl2
      with introduce forall (i : Fin.fin (length v2) {Some? (f_eq i)}) . sl2 i === sl1 (Some?.v (f_eq i))
      with assert (f_eq i == vequiv_trans_eq1_restr_f e0 (index e1.veq_eq i))


(***** [vequiv_cons] *)

let vequiv_cons_typ (hd : Type) (#pre #post : Fl.ty_list) (e : veq_eq_t_list (length pre) (length post))
  =
    let f_eq = U.cast (veq_eq_t (length (hd :: pre)) (length (hd :: post))) (veq_of_list (vequiv_cons_eq e)) in
    introduce forall (i : Fin.fin (length (hd :: post)) {Some? (f_eq i)}) .
              index (hd :: post) i == index (hd :: pre) (Some?.v (f_eq i))
      with if i > 0 then begin
        let Some j = index e (i-1) in
        assert (index post (i-1) == index pre j)
      end

#push-options "--ifuel 0 --z3rlimit 20"
let vequiv_cons_g (hd : vprop') (#pre #post : vprop_list) (e : vequiv pre post) (opened : Mem.inames)
  =
    elim_vpl_cons hd pre;
    let x = gget' hd in
    let sl_pre = gget_f pre in
    Fl.tail_cons (Ghost.reveal x) sl_pre;
    e.veq_g opened;
    let sl_post = gget_f post in
    Fl.tail_cons (Ghost.reveal x) sl_post;
    intro_vpl_cons hd post
#pop-options


(***** [vequiv_app] *)

#push-options "--ifuel 0 --z3rlimit 20"
let vequiv_app_typ
      (#pre0 #post0 : Fl.ty_list) (e0 : veq_eq_t_list (length pre0) (length post0))
      (#pre1 #post1 : Fl.ty_list) (e1 : veq_eq_t_list (length pre1) (length post1))
  =
    let pre0_n  = length pre0  in
    let pre1_n  = length pre1  in
    let post0_n = length post0 in
    let post1_n = length post1 in
    let e0' = map (Opt.map (fin_shift pre0_n   0    (pre0_n + pre1_n))) e0 in
    let e1' = map (Opt.map (fin_shift pre1_n pre0_n (pre0_n + pre1_n))) e1 in
    let f_eq = U.cast (veq_eq_t (length (pre0 @ pre1)) (length (post0 @ post1)))
                      (veq_of_list (vequiv_app_eq e0 e1))
    in
    introduce forall (i : Fin.fin (length (post0 @ post1)) {Some? (f_eq i)}) .
              (index (post0 @ post1) i == index (pre0 @ pre1) (Some?.v (f_eq i)))
      with begin
        Ll.append_index e0' e1' i;
        Ll.append_index post0 post1 i;
        Ll.append_index pre0  pre1  (Some?.v (f_eq i));
        if i < post0_n
        then begin
          let Some j = index e0 i in
          assert (f_eq i = Some j)
        end else begin
          let Some j = index e1 (i - post0_n) in
          assert (f_eq i = Some (j + pre0_n))
        end
      end
#pop-options

#push-options "--ifuel 0 --z3rlimit 20"
let vequiv_app_sl_eq
      (#pre0 #post0 : Fl.ty_list) (e0 : veq_eq_t_list (length pre0) (length post0))
      (#pre1 #post1 : Fl.ty_list) (e1 : veq_eq_t_list (length pre1) (length post1))
      (sl0_0 : Fl.flist pre0)  (sl0_1 : Fl.flist pre1)
      (sl1_0 : Fl.flist post0) (sl1_1 : Fl.flist post1)
  =
    let f_eq = U.cast (veq_eq_t (length (pre0 @ pre1)) (length (post0 @ post1)))
                      (veq_of_list (vequiv_app_eq e0 e1))
    in
    introduce forall (i : Fin.fin (length (post0 @ post1)) {Some? (f_eq i)}) .
              Fl.append sl1_0 sl1_1 i === Fl.append sl0_0 sl0_1 (Some?.v (f_eq i))
      with begin
        Ll.pat_append ();
        if i < length post0
        then begin
          let Some j = index e0 i in
          assert (f_eq i = Some j)
        end else begin
          let Some j = index e1 (i - length post0) in
          assert (f_eq i = Some (j + length pre0))
        end
      end
#pop-options

#push-options "--ifuel 0 --z3rlimit 10"
let vequiv_app_g
      (#pre0 #post0 : vprop_list) (e0 : vequiv pre0 post0)
      (#pre1 #post1 : vprop_list) (e1 : vequiv pre1 post1)
      (opened : Mem.inames)
  =
    elim_vpl_append pre0 pre1;
    let sl0_0 = gget_f pre0  in
    let sl0_1 = gget_f pre1  in
    Fl.append_splitAt_ty (vprop_list_sels_t pre0) (vprop_list_sels_t pre1) sl0_0 sl0_1;
    e0.veq_g opened;
    e1.veq_g opened;
    let sl1_0 = gget_f post0 in
    let sl1_1 = gget_f post1 in
    Fl.append_splitAt_ty (vprop_list_sels_t post0) (vprop_list_sels_t post1) sl1_0 sl1_1;
    intro_vpl_append post0 post1;

    vequiv_app_sl_eq
      #(vprop_list_sels_t pre0) #(vprop_list_sels_t post0) (U.cast _ e0.veq_eq)
      #(vprop_list_sels_t pre1) #(vprop_list_sels_t post1) (U.cast _ e1.veq_eq)
      sl0_0 sl0_1 sl1_0 sl1_1;
    Ll.map_append Mkvprop'?.t pre0  pre1;
    Ll.map_append Mkvprop'?.t post0 post1;
    assert (vprop_list_sels_t (pre0 @ pre1) == (vprop_list_sels_t pre0 @ vprop_list_sels_t pre1))
        by T.(norm [delta_only [`%vprop_list_sels_t]]; smt ());
    assert (vprop_list_sels_t (post0 @ post1) == (vprop_list_sels_t post0 @ vprop_list_sels_t post1))
        by T.(norm [delta_only [`%vprop_list_sels_t]]; smt ())
#pop-options


(***** [vequiv_of_perm] *)

#push-options "--ifuel 0"
let vequiv_of_perm_sel_eq
      (#pre #post : vprop_list) (f : vequiv_perm pre post)
      (sl0 : sl_f pre) (sl1 : sl_f post)
  : squash (veq_sel_eq (veq_eq_sl (vequiv_of_perm_eq f)) sl0 sl1 <==> sl1 == extract_vars f sl0)
  =
    introduce _ /\ _
      with introduce _ ==> _ with _ .
           Fl.flist_extensionality sl1 (extract_vars f sl0) (fun i -> ())
       and ()

let vequiv_of_perm_g #pre #post f opened = change_vpl_perm f
#pop-options


(***** [vequiv_inj] *)

(**) private let __begin_vequiv_inj = ()

let rec mem_Some_eq (#a : eqtype) (x : a) (l : list (option a))
  : Lemma (ensures mem_Some x l = mem (Some x) l) (decreases l) [SMTPat (mem_Some x l)]
  = match l with
  | [] -> ()
  | y :: ys -> mem_Some_eq x ys

#push-options "--ifuel 1 --fuel 0"
let ij_matched_perm_f_injective
      (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (Perm.injective (ij_matched_perm_f ij))
  = Perm.injectiveI (ij_matched_perm_f ij) (fun i1 i1' ->
      let nm_src = mask_not (ij_src_mask ij) in
      // FIXME we cannot use [nm_src] here
      let i0  = mask_pull (mask_not (ij_src_mask ij)) i1  in
      let i0' = mask_pull (mask_not (ij_src_mask ij)) i1' in
      let j0  = Some?.v (index ij i0 ) in
      let j0' = Some?.v (index ij i0') in
      (**) lemma_index_memP ij i0;
      (**) lemma_index_memP ij i0';
      let nm_trg = mask_not (ij_trg_mask ij) in
      mask_pull_push nm_trg j0;
      mask_pull_push nm_trg j0';
      assert (j0 == j0');
      assert (i0 == i0');
      Perm.inv_l_injective (mask_pull nm_src) (mask_push nm_src);
      assert (i1 == i1')
  )

let ij_matched_perm_f_surjective
      (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (Perm.surjective (ij_matched_perm_f ij))
  = Perm.surjectiveI (ij_matched_perm_f ij) (fun (j1 : Fin.fin (mask_len (mask_not (ij_trg_mask ij)))) ->
      let j0 = mask_pull (mask_not (ij_trg_mask ij)) j1 in
      let i0 = Ll.mem_findi (Some j0) ij in
      mask_push (mask_not (ij_src_mask ij)) i0
  )

let ij_matched_len (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (mask_len (mask_not (ij_trg_mask ij)) = mask_len (mask_not (ij_src_mask ij)))
  =
    ij_matched_perm_f_injective ij;
    Perm.fin_injective_le  _ _ (ij_matched_perm_f ij);
    ij_matched_perm_f_surjective ij;
    Perm.fin_surjective_ge _ _ (ij_matched_perm_f ij)
#pop-options

#push-options "--ifuel 1 --fuel 1 --z3rlimit 120"
let ij_matched_perm_eq (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (ij_matched_len ij;
           filter_mask (mask_not (ij_src_mask ij)) src ==
           Perm.apply_perm_r (ij_matched_perm ij) (filter_mask (mask_not (ij_trg_mask ij)) trg))
  =
    let l_src = filter_mask (mask_not (ij_src_mask ij)) src in
    let l_trg = filter_mask (mask_not (ij_trg_mask ij)) trg in
    let p = ij_matched_perm ij in
    ij_matched_len ij;
    Ll.list_extensionality (Perm.apply_perm_r p l_trg) l_src begin fun i1 ->
      let i0 = mask_pull (mask_not (ij_src_mask ij)) i1 in
      let j0 = Some?.v (index ij i0) in
      lemma_index_memP ij i0;
      calc (==) {
        index (Perm.apply_perm_r p l_trg) i1;
      == { }
        index l_trg (p i1);
      == { }
        index (filter_mask (mask_not (ij_trg_mask ij)) trg)
                (mask_push (mask_not (ij_trg_mask ij)) j0);
      == { }
        index trg j0;
      == { }
        index src i0;
      == { }
        index l_src i1;
      }
    end
#pop-options


#push-options "--ifuel 0 --fuel 0 --z3rlimit 10"
let vequiv_inj_typ
      (#src #trg : vprop_list)
      (ij : partial_injection src trg)
      (e' : vequiv (filter_mask (ij_trg_mask ij) trg) (filter_mask (ij_src_mask ij) src))
  : squash (veq_typ_eq (vprop_list_sels_t trg) (vprop_list_sels_t src)
                           (U.cast _ (veq_of_list (vequiv_inj_eq ij e'))))
  =
    let mask_src = ij_src_mask ij                in
    let mask_trg = ij_trg_mask ij                in
    let src' = filter_mask mask_src src          in
    let trg' = filter_mask mask_trg trg          in
    let f_eq = veq_of_list (vequiv_inj_eq ij e') in
    introduce forall (i : Fin.fin (length src) {Some? (f_eq i)}) .
              (index src i).t == (index trg (Some?.v (f_eq i))).t
      with if index mask_src i
      then begin
        calc (==) {
          (index trg (Some?.v (f_eq i))).t;
        == {}
          (index trg (mask_pull mask_trg (Some?.v (veq_f e' (mask_push mask_src i))))).t;
        == { }
          (index trg' (Some?.v (veq_f e' (mask_push mask_src i)))).t;
        == { elim_veq_typ_eq e'.veq_typ (mask_push mask_src i)}
          (index src' (mask_push mask_src i)).t;
        == { }
          (index src i).t;
        }
      end
#pop-options

#push-options "--ifuel 0 --fuel 0 --z3rlimit 30"
let vequiv_inj_g_lemma #src #trg ij e'
      (sl0 : sl_f trg) (sl1 : sl_f src)
  : Lemma (requires filter_sl (mask_not (ij_src_mask ij)) sl1
                      == extract_vars (ij_matched_equiv ij) (filter_sl (mask_not (ij_trg_mask ij)) sl0) /\
                    veq_sel_eq (veq_eq_sl (veq_f e')) (filter_sl (ij_trg_mask ij) sl0)
                                                      (filter_sl (ij_src_mask ij) sl1))
          (ensures  veq_sel_eq (veq_eq_sl (veq_of_list (vequiv_inj_eq #src #trg ij e'))) sl0 sl1)
  =
    let mask_src = ij_src_mask ij                    in
    let mask_trg = ij_trg_mask ij                    in
    let f_eq     = veq_of_list (vequiv_inj_eq ij e') in
    let sl0_nm   = filter_sl (mask_not mask_trg) sl0 in        
    let sl1_m    = filter_sl           mask_src  sl1 in
    let sl1_nm   = filter_sl (mask_not mask_src) sl1 in
    introduce forall (i0 : Fin.fin (length src) {Some? (f_eq i0)}) .
              sl1 i0 === sl0 (Some?.v (f_eq i0))
    with begin
      if index mask_src i0
      then begin
        let i1 = mask_push mask_src i0 in
        let Some j1 = veq_f e' i1      in
        let j0 = mask_pull mask_trg j1 in
        calc (==) {
          (|_, sl1 i0|) <: t:Type&t;
        == { }
          (|_, sl1_m i1|);
        == { }
          (|_, filter_sl (ij_trg_mask ij) sl0 j1|);
        == { }
          (|_, sl0 j0|);
        }
      end else begin
        assert (f_eq i0 == index ij i0);
        let Some j0 = index ij i0 in
        (**) lemma_index_memP ij i0;
        let i1 = mask_push (mask_not mask_src) i0 in
        let j1 = mask_push (mask_not mask_trg) j0 in
        calc (==) {
          (|_, sl1 i0|) <: t:Type&t;
        == { }
          (|_, sl1_nm i1|);
        == { }
          (|_, extract_vars (ij_matched_equiv ij) sl0_nm i1|);
        == { }
          (|_, sl0_nm (ij_matched_equiv ij i1)|);
        == { assert (ij_matched_equiv ij i1 == j1) }
          (|_, sl0_nm j1|);
        == { }
          (|_, sl0 j0|);
        }
      end
    end
#pop-options

#push-options "--ifuel 0 --fuel 0 --z3rlimit 20"
let vequiv_inj_g #src #trg ij e' opened
  =
    (**) let sl0 = gget_f trg     in
    intro_vpl_filter_mask trg (ij_trg_mask ij);
    e'.veq_g opened;
    change_vpl_perm (ij_matched_equiv ij);
    elim_vpl_filter_mask src (ij_src_mask ij);
    (**) let sl1 = gget_f src     in
    (**) vequiv_inj_g_lemma ij e' sl0 sl1
#pop-options


let extend_partial_injection_src #a (#src #trg : list a) (ij : partial_injection src trg) (src_add : list a)
  : Lemma (filter_mask (ij_src_mask (extend_partial_injection ij src_add)) (src@src_add)
        == append (filter_mask (ij_src_mask ij) src) src_add)
  =
    let f_add = map (fun _ -> None) src_add in
    let m_add = ij_src_mask #(length src_add) f_add in
    Ll.map_append None? ij f_add;
    filter_mask_append (ij_src_mask ij) m_add src src_add;
    filter_mask_true m_add src_add (fun i -> ())

let extend_partial_injection_trg #a (#src #trg : list a) (ij : partial_injection src trg) (src_add : list a)
  : Lemma (filter_mask (ij_trg_mask (extend_partial_injection ij src_add)) trg
        == filter_mask (ij_trg_mask ij) trg)
  = 
    let f_add = map (fun _ -> None) src_add in
    Ll.list_extensionality (ij_trg_mask (extend_partial_injection ij src_add)) (ij_trg_mask ij) (fun j ->
      append_mem ij f_add (Some j);
      if mem (Some j) f_add then (
        let i = Ll.mem_findi (Some j) f_add in
        false_elim ()
    ))
