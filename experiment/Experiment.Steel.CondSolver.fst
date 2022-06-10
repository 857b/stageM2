module Experiment.Steel.CondSolver

module L  = FStar.List.Pure
module Fl = Learn.FList

open Learn.List.Mask
open Steel.Effect
open Steel.Effect.Atomic

#set-options "--fuel 1 --ifuel 1"


(***** [truth_refl] *)

let rec truth_refl_list_length (#ps : list prop) (#bs : list bool) (rfl : truth_refl_list ps bs)
  : Lemma (ensures L.length ps = L.length bs) (decreases rfl)
  = match rfl with
    | ReflLNil -> ()
    | ReflLTrue rfl | ReflLFalse _ rfl -> truth_refl_list_length rfl

let rec truth_refl_list_index (#ps : list prop) (#bs : list bool) (rfl : truth_refl_list ps bs)
                              (i : Fin.fin (L.length bs))
  : Lemma (requires L.index bs i) (ensures L.length ps = L.length bs /\ L.index ps i) (decreases rfl)
  = truth_refl_list_length rfl;
  match rfl with
  | ReflLTrue    rfl -> if i > 0 then truth_refl_list_index rfl (i - 1)
  | ReflLFalse _ rfl -> truth_refl_list_index rfl (i - 1)

(**) #push-options "--ifuel 2"
(**) private let __begin_opt_0 = ()
(**) #pop-options
(**) private let __end_opt_0 = ()


(***** [build_to_repr_t] *)

let __build_to_repr_t_lem
      (p : SE.vprop) (r_p : M.vprop_list {p `SE.equiv` M.vprop_of_list r_p}) (h : SE.rmem p)
      (v : SE.vprop{SE.can_be_split p v}) (_ : squash (SE.VUnit? v))
      (i : elem_index (SE.VUnit?._0 v) r_p)
      (i' : int) (_ : squash (i' == i))
  : squash (h v ==
        M.sel r_p (SE.equiv_can_be_split p (M.vprop_of_list r_p);
                   SE.focus_rmem h (M.vprop_of_list r_p)) i)
  =
    SE.equiv_can_be_split p (M.vprop_of_list r_p);
    let h_r = SE.focus_rmem h (M.vprop_of_list r_p) in
    M.vprop_of_list_can_be_split r_p i;
    calc (==) {
      M.sel r_p h_r i;
    == { M.sel_eq' }
      M.sel_f' r_p h_r i;
    == { }
      h_r (SE.VUnit (L.index r_p i));
    == { }
      h v;
    }

(**) #push-options "--ifuel 2"
(**) private let __begin_opt_1 = ()
(**) #pop-options
(**) private let __end_opt_1 = ()


(***** [build_injection] *)

let rec check_injective_on_dom_aux_spec (#b : eqtype) (f : list (option b))
  : Lemma (ensures (let ij, rng = check_injective_on_dom_aux f in
                   (ij ==> injective_on_dom #(Fin.fin (len f)) (L.index f)) /\
                   (forall (y : b) . L.mem (Some y) f ==> L.mem y rng)))
          (decreases f)
  = match f with
  | [] -> ()
  | None :: fs    ->
      let ij, rng = check_injective_on_dom_aux fs in
      check_injective_on_dom_aux_spec fs;
      if ij
      then injective_on_domI #(Fin.fin (len f)) (L.index f) (fun i i' ->
        assert (L.index f i  == L.index fs (i -1));
        assert (L.index f i' == L.index fs (i'-1)))
  | Some y :: fs ->
      let ij, rng = check_injective_on_dom_aux fs in
      check_injective_on_dom_aux_spec fs;
      if ij && not (L.mem y rng)
      then injective_on_domI #(Fin.fin (len f)) (L.index f) (fun i i' ->
        if i > 0 then begin
          assert (L.index f i == L.index fs (i-1));
          L.lemma_index_memP fs (i-1)
        end;
        if i' > 0 then begin
          assert (L.index f i' == L.index fs (i'-1));
          L.lemma_index_memP fs (i'-1)
        end)

let rec build_injection_find_spec (#trg_n : nat) (g mask : Ll.vec trg_n bool) (i : nat)
  : Lemma (requires Some? (build_injection_find g mask i))
          (ensures (let j = Some?.v (build_injection_find g mask i) - i in
                    j >= 0 /\ L.index g j /\ L.index mask j))
          (decreases trg_n)
  = match g, mask with
  | [], [] | true :: _, true :: _ -> ()
  | _ :: g, _ :: mask -> build_injection_find_spec #(trg_n-1) g mask (i+1)

let rec build_injection_iter_spec (#src_n #trg_n : nat) (g : ograph src_n trg_n) (mask : Ll.vec trg_n bool)
  : Lemma (ensures (let res = build_injection_iter g mask in
                   (forall (i : Fin.fin src_n) . {:pattern (L.index res i)}
                      Some? (L.index res i) ==> (L.index (L.index g i) (Some?.v (L.index res i))
                                             && L.index mask (Some?.v (L.index res i)))) /\
                   injective_on_dom #(Fin.fin src_n) (L.index res)))
          (decreases g)
  = match g with
  | [] -> ()
  | g0 :: g -> let y = build_injection_find g0 mask 0 in
             match y with
             | Some y -> build_injection_find_spec g0 mask 0;
                        let mask' = Ll.set y false mask                     in
                        let res'  = build_injection_iter #(src_n-1) g mask' in
                        let res   = Some y :: res'                           in
                        build_injection_iter_spec #(src_n-1) g mask';
                        injective_on_domI #(Fin.fin src_n) (L.index res) (fun i j ->
                          if i > 0 && j > 0 then ()
                          else if i = 0 && j = 0 then ()
                          else false_elim ()
                        )
             | None   -> let res'  = build_injection_iter #(src_n-1) g mask in
                        let res   = None :: res'                            in
                        build_injection_iter_spec #(src_n-1) g mask;
                        injective_on_domI #(Fin.fin src_n) (L.index res) (fun i j ->
                          assert (i > 0 && j > 0)
                        )

let rec list_of_equalities_length (#a : Type) (src trg : list a)
  : Lemma (ensures len (list_of_equalities src trg) = len src * len trg) (decreases src)
          [SMTPat (L.length (list_of_equalities src trg))]
  = match src with
  | [] -> ()
  | x :: xs -> let p0 = L.map #_ #prop (fun y -> (x == y)) trg in
             // needed for [append_length] to trigger
             // ?because flatten is defined with [append] instead of [@]
             assert (list_of_equalities (x :: xs) trg
                  == L.(p0 @ list_of_equalities xs trg))
                 by (trefl ());
             list_of_equalities_length xs trg

#push-options "--z3rlimit 60 --z3refresh"
let rec list_of_equalities_index (#a : Type) (src trg : list a) (i : Fin.fin (len src)) (j : Fin.fin (len trg))
  : Lemma (ensures i * len trg + j < len (list_of_equalities src trg) /\
                   L.index (list_of_equalities src trg) (i * len trg + j) == (L.index src i == L.index trg j))
          (decreases i)
  = 
    let x :: xs = src in
    let p0 = L.map #_ #prop (fun y -> (x == y)) trg in
    assert (list_of_equalities (x :: xs) trg == L.(p0 @ list_of_equalities xs trg))
        by (trefl ());
    Ll.append_index p0 (list_of_equalities xs trg) (i * len trg + j);
    if i > 0 then list_of_equalities_index xs trg (i - 1) j
#pop-options

// FIXME: With a lower rlimit Z3 sometimes times out in a few seconds
#push-options "--z3rlimit 1000 --z3refresh"
let rec list_to_matrix_index (#a : Type) (n0 n1 : nat) (l : Ll.vec (n0 * n1) a) (i : Fin.fin n0) (j : Fin.fin n1)
  : Lemma (ensures i * n1 + j < n0 * n1 /\
                   L.index (L.index (list_to_matrix n0 n1 l) i) j == L.index l (i * n1 + j))
          (decreases n0)
          [SMTPat (L.index (L.index (list_to_matrix n0 n1 l) i) j)]
  = let l0, ls = L.splitAt n1 l in
    L.splitAt_length n1 l;
    if i = 0 then L.lemma_splitAt_reindex_left n1 l j
    else begin
      list_to_matrix_index (n0 - 1) n1 ls (i - 1) j;
      L.lemma_splitAt_reindex_right n1 l ((i - 1) * n1 + j)
    end
#pop-options

let ograph_of_equalities_index (#a : Type) (src trg : list a) (bs : list bool)
      (rfl : truth_refl_list (list_of_equalities src trg) bs)
      (i : Fin.fin (len src)) (j : Fin.fin (len trg))
  : Lemma (requires L.index (L.index (ograph_of_equalities src trg bs rfl) i) j)
          (ensures  L.index src i == L.index trg j)
  =
    (**) truth_refl_list_length rfl;
    calc (==>) {
      b2t (L.index (L.index (ograph_of_equalities src trg bs rfl) i) j);
    == { }
      b2t (L.index (L.index (list_to_matrix (len src) (len trg) bs) i) j);
    == { }
      b2t (L.index bs (i * len trg + j));
    ==> { truth_refl_list_index rfl (i * len trg + j) }
      L.index (list_of_equalities src trg) (i * len trg + j);
    == { list_of_equalities_index src trg i j }
      L.index src i == L.index trg j;
    }

(**) #push-options "--ifuel 2"
(**) private let __begin_opt_2 = ()
(**) #pop-options
(**) private let __end_opt_2 = ()

let rec check_map_to_eq_spec (#a : Type) (src trg : list a) (ij : Ll.vec (len src) (option (Fin.fin (len trg))))
  : Lemma (requires check_map_to_eq src trg ij)
          (ensures map_to_eq src trg (L.index ij)) (decreases ij)
  = match ij with
  | [] -> ()
  | None   :: ij' -> let _  :: tl = src in
                   check_map_to_eq_spec tl trg ij';
                   introduce forall (i : Fin.fin (len src) {Some? (L.index ij i)}).
                         L.index trg (Some?.v (L.index ij i)) == L.index src i
                     with assert (L.index ij i == L.index ij' (i-1) /\ L.index src i == L.index tl (i-1))
  | Some i :: ij' -> let hd :: tl = src in
                   check_map_to_eq_spec tl trg ij';
                   introduce forall (i : Fin.fin (len src) {Some? (L.index ij i)}).
                         L.index trg (Some?.v (L.index ij i)) == L.index src i
                     with if i > 0
                          then assert (L.index ij i == L.index ij' (i-1) /\ L.index src i == L.index tl (i-1))

(***** [vequiv_sol] *)

let rec mem_Some_eq (#a : eqtype) (x : a) (l : list (option a))
  : Lemma (ensures mem_Some x l = L.mem (Some x) l) (decreases l) [SMTPat (mem_Some x l)]
  = match l with
  | [] -> ()
  | y :: ys -> mem_Some_eq x ys

#push-options "--ifuel 1 --fuel 0"
let ij_matched_perm_f_injective
      (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (Perm.injective (ij_matched_perm_f ij))
  = Perm.injectiveI (ij_matched_perm_f ij) (fun i1 i1' ->
      let nm_src = Msk.mask_not (ij_src_mask ij) in
      // FIXME we cannot use [nm_src] here
      let i0  = Msk.mask_pull (Msk.mask_not (ij_src_mask ij)) i1  in
      let i0' = Msk.mask_pull (Msk.mask_not (ij_src_mask ij)) i1' in
      let j0  = Some?.v (L.index ij i0 ) in
      let j0' = Some?.v (L.index ij i0') in
      (**) L.lemma_index_memP ij i0;
      (**) L.lemma_index_memP ij i0';
      let nm_trg = Msk.mask_not (ij_trg_mask ij) in
      Msk.mask_pull_push nm_trg j0;
      Msk.mask_pull_push nm_trg j0';
      assert (j0 == j0');
      assert (i0 == i0');
      Perm.inv_l_injective (Msk.mask_pull nm_src) (Msk.mask_push nm_src);
      assert (i1 == i1')
  )

let ij_matched_perm_f_surjective
      (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (Perm.surjective (ij_matched_perm_f ij))
  = Perm.surjectiveI (ij_matched_perm_f ij) (fun (j1 : Fin.fin (Msk.mask_len (Msk.mask_not (ij_trg_mask ij)))) ->
      let j0 = Msk.mask_pull (Msk.mask_not (ij_trg_mask ij)) j1 in
      let i0 = Ll.mem_findi (Some j0) ij in
      Msk.mask_push (Msk.mask_not (ij_src_mask ij)) i0
  )

let ij_matched_len (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (Msk.mask_len (Msk.mask_not (ij_trg_mask ij)) = Msk.mask_len (Msk.mask_not (ij_src_mask ij)))
  =
    ij_matched_perm_f_injective ij;
    Perm.fin_injective_le  _ _ (ij_matched_perm_f ij);
    ij_matched_perm_f_surjective ij;
    Perm.fin_surjective_ge _ _ (ij_matched_perm_f ij)
#pop-options

#push-options "--ifuel 1 --fuel 1 --z3rlimit 120"
let ij_matched_perm_eq (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (ij_matched_len ij;
           Msk.filter_mask (Msk.mask_not (ij_src_mask ij)) src ==
           Perm.apply_perm_r (ij_matched_perm ij) (Msk.filter_mask (Msk.mask_not (ij_trg_mask ij)) trg))
  =
    let l_src = Msk.filter_mask (Msk.mask_not (ij_src_mask ij)) src in
    let l_trg = Msk.filter_mask (Msk.mask_not (ij_trg_mask ij)) trg in
    let p = ij_matched_perm ij in
    ij_matched_len ij;
    Ll.list_extensionality (Perm.apply_perm_r p l_trg) l_src begin fun i1 ->
      let i0 = Msk.mask_pull (Msk.mask_not (ij_src_mask ij)) i1 in
      let j0 = Some?.v (L.index ij i0) in
      L.lemma_index_memP ij i0;
      calc (==) {
        L.index (Perm.apply_perm_r p l_trg) i1;
      == { }
        L.index l_trg (p i1);
      == { }
        L.index (Msk.filter_mask (Msk.mask_not (ij_trg_mask ij)) trg)
                (Msk.mask_push (Msk.mask_not (ij_trg_mask ij)) j0);
      == { }
        L.index trg j0;
      == { }
        L.index src i0;
      == { }
        L.index l_src i1;
      }
    end
#pop-options


#push-options "--ifuel 0 --fuel 0 --z3rlimit 10"
let vequiv_inj_typ
      (#src #trg : M.vprop_list)
      (ij : partial_injection src trg)
      (e' : M.vequiv (filter_mask (ij_trg_mask ij) trg) (filter_mask (ij_src_mask ij) src))
  : squash (M.veq_typ_eq (M.vprop_list_sels_t trg) (M.vprop_list_sels_t src)
                         (U.cast _ (M.veq_of_list (vequiv_inj_eq ij e'))))
  =
    let mask_src = ij_src_mask ij                  in
    let mask_trg = ij_trg_mask ij                  in
    let src' = filter_mask mask_src src            in
    let trg' = filter_mask mask_trg trg            in
    let f_eq = M.veq_of_list (vequiv_inj_eq ij e') in
    introduce forall (i : Fin.fin (len src) {Some? (f_eq i)}) . (L.index src i).t == (L.index trg (Some?.v (f_eq i))).t
      with if L.index mask_src i
      then begin
        calc (==) {
          (L.index trg (Some?.v (f_eq i))).t;
        == {}
          (L.index trg (mask_pull mask_trg (Some?.v (M.veq_f e' (mask_push mask_src i))))).t;
        == { }
          (L.index trg' (Some?.v (M.veq_f e' (mask_push mask_src i)))).t;
        == { M.elim_veq_typ_eq e'.veq_typ (mask_push mask_src i)}
          (L.index src' (mask_push mask_src i)).t;
        == { }
          (L.index src i).t;
        }
      end
#pop-options

#push-options "--ifuel 1 --z3rlimit 20"
// ALT? use steel equiv
let rec intro_filter_mask #opened (vs : M.vprop_list) (mask : Ll.vec (L.length vs) bool)
  : SteelGhost unit opened
      (M.vprop_of_list vs)
      (fun () -> M.vprop_of_list (filter_mask mask vs) `star`
              M.vprop_of_list (filter_mask (Msk.mask_not mask) vs))
      (requires fun _ -> True) (ensures fun h0 () h1 ->
          M.sel_list (filter_mask mask vs) h1 == filter_mask_dl mask _ (M.sel_list vs h0) /\
          M.sel_list (filter_mask (Msk.mask_not mask) vs) h1 ==
            filter_mask_dl (Msk.mask_not mask) _ (M.sel_list vs h0))
      (decreases vs)
  = match mask, vs with
  | [], [] ->
        change_equal_slprop
           (M.vprop_of_list vs `star` emp)
           (M.vprop_of_list (filter_mask mask vs) `star`
            M.vprop_of_list (filter_mask (Msk.mask_not mask) vs))
  | true  :: mask', v0 :: vs' ->
        (**) let mask' : Ll.vec (L.length vs') bool = mask' in
        (**) let sl0 : Ghost.erased (t_of (M.vprop_of_list vs)) = gget (M.vprop_of_list vs) in
        (**) let l0  : M.sl_list vs = M.vpl_sels vs sl0 in
        change_equal_slprop (M.vprop_of_list vs) (VUnit v0 `star` M.vprop_of_list vs');
        intro_filter_mask vs' mask';
        change_equal_slprop (VUnit v0 `star` M.vprop_of_list (filter_mask mask' vs'))
                            (M.vprop_of_list (filter_mask mask vs));
        change_equal_slprop (M.vprop_of_list (filter_mask (Msk.mask_not mask') vs'))
                            (M.vprop_of_list (filter_mask (Msk.mask_not mask ) vs ));
        (**) let sl1_t : Ghost.erased (t_of (M.vprop_of_list (filter_mask mask vs)))
        (**)           = gget (M.vprop_of_list (filter_mask mask vs)) in
        (**) let sl1_f : Ghost.erased (t_of (M.vprop_of_list (filter_mask (Msk.mask_not mask) vs)))
        (**)           = gget (M.vprop_of_list (filter_mask (Msk.mask_not mask) vs)) in
        (**) let l1_t  : M.sl_list (filter_mask mask vs) = M.vpl_sels (filter_mask mask vs) sl1_t in
        (**) let l1_t' : M.sl_list (filter_mask mask vs) = U.cast _ (filter_mask_dl mask _ l0) in
        (**) assert (l1_t == l1_t');
        (**) assert (M.vpl_sels _ sl1_f === filter_mask_dl (Msk.mask_not mask) _ l0)
  | false :: mask', v0 :: vs' ->
        (**) let mask' : Ll.vec (L.length vs') bool = mask' in
        (**) let sl0 = gget (M.vprop_of_list vs)            in
        (**) let l0  : M.sl_list vs = M.vpl_sels vs sl0     in
        change_equal_slprop (M.vprop_of_list vs) (VUnit v0 `star` M.vprop_of_list vs');
        intro_filter_mask vs' mask';
        change_equal_slprop (M.vprop_of_list (filter_mask mask' vs'))
                            (M.vprop_of_list (filter_mask mask vs));
        change_equal_slprop (VUnit v0 `star` M.vprop_of_list (filter_mask (Msk.mask_not mask') vs'))
                            (M.vprop_of_list (filter_mask (Msk.mask_not mask) vs));
        (**) let sl1_t = gget (M.vprop_of_list (filter_mask mask vs))                in
        (**) let sl1_f = gget (M.vprop_of_list (filter_mask (Msk.mask_not mask) vs)) in
        (**) assert (M.vpl_sels _ sl1_t === filter_mask_dl mask _ l0);
        (**) assert (M.vpl_sels _ sl1_f === filter_mask_dl (Msk.mask_not mask) _ l0)

let rec elim_filter_mask #opened (vs : M.vprop_list) (mask : Ll.vec (L.length vs) bool)
  : SteelGhost unit opened
      (M.vprop_of_list (filter_mask mask vs) `star`
       M.vprop_of_list (filter_mask (Msk.mask_not mask) vs))
      (fun () -> M.vprop_of_list vs)
      (requires fun _ -> True) (ensures fun h0 () h1 ->
          M.sel_list (filter_mask mask vs) h0 == filter_mask_dl mask _ (M.sel_list vs h1) /\
          M.sel_list (filter_mask (Msk.mask_not mask) vs) h0 ==
            filter_mask_dl (Msk.mask_not mask) _ (M.sel_list vs h1))
      (decreases vs)
  = match mask, vs with
  | [], [] ->
        change_equal_slprop
           (M.vprop_of_list (filter_mask mask vs) `star`
            M.vprop_of_list (filter_mask (Msk.mask_not mask) vs))
           (M.vprop_of_list vs `star` emp)
  | true  :: mask', v0 :: vs' ->
        (**) let mask' : Ll.vec (L.length vs') bool = mask' in
        (**) let sl1_t : Ghost.erased (t_of (M.vprop_of_list (filter_mask mask vs)))
        (**)           = gget (M.vprop_of_list (filter_mask mask vs)) in
        (**) let sl1_f : Ghost.erased (t_of (M.vprop_of_list (filter_mask (Msk.mask_not mask) vs)))
        (**)           = gget (M.vprop_of_list (filter_mask (Msk.mask_not mask) vs)) in
        change_equal_slprop (M.vprop_of_list (filter_mask mask vs))
                            (VUnit v0 `star` M.vprop_of_list (filter_mask mask' vs'));
        change_equal_slprop (M.vprop_of_list (filter_mask (Msk.mask_not mask ) vs ))
                            (M.vprop_of_list (filter_mask (Msk.mask_not mask') vs'));
        elim_filter_mask vs' mask';
        change_equal_slprop (VUnit v0 `star` M.vprop_of_list vs') (M.vprop_of_list vs);
        (**) let sl0 : Ghost.erased (t_of (M.vprop_of_list vs)) = gget (M.vprop_of_list vs) in
        (**) let l0  : M.sl_list vs = M.vpl_sels vs sl0 in
        (**) assert (M.vpl_sels (filter_mask mask vs) sl1_t === filter_mask_dl mask _ l0);
        (**) assert (M.vpl_sels _ sl1_f === filter_mask_dl (Msk.mask_not mask) _ l0)
  | false :: mask', v0 :: vs' ->
        (**) let mask' : Ll.vec (L.length vs') bool = mask'           in
        (**) let sl1_t = gget (M.vprop_of_list (filter_mask mask vs)) in
        (**) let sl1_f = gget (M.vprop_of_list (filter_mask (Msk.mask_not mask) vs)) in
        change_equal_slprop (M.vprop_of_list (filter_mask mask vs))
                            (M.vprop_of_list (filter_mask mask' vs'));
        change_equal_slprop (M.vprop_of_list (filter_mask (Msk.mask_not mask) vs))
                            (VUnit v0 `star` M.vprop_of_list (filter_mask (Msk.mask_not mask') vs'));
        elim_filter_mask vs' mask';
        change_equal_slprop (VUnit v0 `star` M.vprop_of_list vs') (M.vprop_of_list vs);
        (**) let sl0 = gget (M.vprop_of_list vs)        in
        (**) let l0  : M.sl_list vs = M.vpl_sels vs sl0 in
        (**) assert (M.vpl_sels _ sl1_t === filter_mask_dl mask _ l0);
        (**) assert (M.vpl_sels _ sl1_f === filter_mask_dl (Msk.mask_not mask) _ l0)
#pop-options

#push-options "--ifuel 1 --fuel 1 --z3rlimit 200"
let vequiv_inj_g_lemma #src #trg ij e'
      (sl0 : M.sl_f trg) (sl1 : M.sl_f src)
  : Lemma (requires filter_mask_fl (mask_not (ij_src_mask ij)) _ sl1
                      == M.extract_vars (ij_matched_equiv ij) (filter_mask_fl (mask_not (ij_trg_mask ij)) _ sl0) /\
                    M.veq_sel_eq (M.veq_eq_sl (M.veq_f e')) (filter_mask_fl (ij_trg_mask ij) _ sl0)
                                                            (filter_mask_fl (ij_src_mask ij) _ sl1))
          (ensures  M.veq_sel_eq (M.veq_eq_sl (M.veq_of_list (vequiv_inj_eq #src #trg ij e'))) sl0 sl1)
  =
    let mask_src = ij_src_mask ij                  in
    let mask_trg = ij_trg_mask ij                  in
    let f_eq = M.veq_of_list (vequiv_inj_eq ij e') in
    introduce forall (i0 : Fin.fin (len src) {Some? (f_eq i0)}) . sl1 i0 === sl0 (Some?.v (f_eq i0))
    with begin
      if L.index mask_src i0
      then begin
        let i1 = mask_push mask_src i0  in
        let j1 = Some?.v (M.veq_f e' i1) in
        let j0 = mask_pull mask_trg j1  in
        assert (f_eq i0 == Some (j0 <: Fin.fin (len trg)));
        assert (sl1 i0 === filter_mask_fl (ij_src_mask ij) _ sl1 i1);
        assert (filter_mask_fl (ij_src_mask ij) _ sl1 i1 === filter_mask_fl (ij_trg_mask ij) _ sl0 j1);
        assert (filter_mask_fl (ij_trg_mask ij) _ sl0 j1 === sl0 j0)
      end else begin
        assert (f_eq i0 == L.index ij i0);
        let sl0' = filter_mask_fl (mask_not mask_trg) _ sl0 in
        let j0 = Some?.v (L.index ij i0) in
        (**) L.lemma_index_memP ij i0;
        let i1 = mask_push (mask_not mask_src) i0 in
        let j1 = mask_push (mask_not mask_trg) j0 in
        assert (sl1 i0 === filter_mask_fl (mask_not mask_src) _ sl1 i1);
        assert (filter_mask_fl (mask_not mask_src) _ sl1 i1 == M.extract_vars (ij_matched_equiv ij) sl0' i1);
        assert (M.extract_vars (ij_matched_equiv ij) sl0' i1 === sl0' (ij_matched_equiv ij i1));
        assert (ij_matched_equiv ij i1 == j1);
        assert (sl0' j1 === sl0 j0)
      end
    end
#pop-options

#push-options "--ifuel 0 --fuel 1"
let vequiv_inj_g #src #trg ij e' opened
  =
    (**) let sl0 = gget (M.vprop_of_list trg) in
    intro_filter_mask trg (ij_trg_mask ij);
    (**) Msk.filter_mask_f_dl_f (ij_trg_mask ij) _ (M.vpl_sels_f _ sl0);
    (**) Msk.filter_mask_f_dl_f (mask_not (ij_trg_mask ij)) _ (M.vpl_sels_f _ sl0);
    e'.veq_g opened;
    M.steel_change_perm (ij_matched_equiv ij);
    elim_filter_mask src (ij_src_mask ij);
    (**) let sl1 = gget (M.vprop_of_list src) in
    (**) Msk.filter_mask_f_dl_f (ij_src_mask ij) _ (M.vpl_sels_f _ sl1);
    (**) Msk.filter_mask_f_dl_f (mask_not (ij_src_mask ij)) _ (M.vpl_sels_f _ sl1);
    (**) vequiv_inj_g_lemma ij e' (M.vpl_sels_f trg sl0) (M.vpl_sels_f src sl1)
#pop-options


let extend_partial_injection_src #a (#src #trg : list a) (ij : partial_injection src trg) (src_add : list a)
  : Lemma (Msk.filter_mask (ij_src_mask (extend_partial_injection ij src_add)) L.(src@src_add)
        == L.append (Msk.filter_mask (ij_src_mask ij) src) src_add)
  =
    let f_add = L.map (fun _ -> None) src_add in
    let m_add = ij_src_mask #(len src_add) f_add in
    Ll.map_append None? ij f_add;
    Msk.filter_mask_append (ij_src_mask ij) m_add src src_add;
    Msk.filter_mask_true m_add src_add (fun i -> ())

let extend_partial_injection_trg #a (#src #trg : list a) (ij : partial_injection src trg) (src_add : list a)
  : Lemma (Msk.filter_mask (ij_trg_mask (extend_partial_injection ij src_add)) trg
        == Msk.filter_mask (ij_trg_mask ij) trg)
  = 
    let f_add = L.map (fun _ -> None) src_add in
    Ll.list_extensionality (ij_trg_mask (extend_partial_injection ij src_add)) (ij_trg_mask ij) (fun j ->
      L.append_mem ij f_add (Some j);
      if L.mem (Some j) f_add then (
        let i = Ll.mem_findi (Some j) f_add in
        false_elim ()
    ))
