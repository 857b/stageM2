module Experiment.Steel.Tac

module L    = FStar.List.Pure
module Fl   = Learn.FList
module Vpl  = Experiment.Steel.VPropList
module Msk  = Learn.List.Mask
module Perm = Learn.Permutation

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
      (p : SE.vprop) (r_p : Vpl.vprop_list {p `SE.equiv` Vpl.vprop_of_list r_p}) (h : SE.rmem p)
      (v : SE.vprop{SE.can_be_split p v}) (_ : squash (SE.VUnit? v))
      (i : elem_index (SE.VUnit?._0 v) r_p)
      (i' : int) (_ : squash (i' == i))
  : squash (h v ==
        Vpl.sel r_p (SE.equiv_can_be_split p (Vpl.vprop_of_list r_p);
                     SE.focus_rmem h (Vpl.vprop_of_list r_p)) i)
  =
    SE.equiv_can_be_split p (Vpl.vprop_of_list r_p);
    let h_r = SE.focus_rmem h (Vpl.vprop_of_list r_p) in
    Vpl.vprop_of_list_can_be_split r_p i;
    calc (==) {
      Vpl.sel r_p h_r i;
    == { Vpl.sel_eq' }
      Vpl.sel_f' r_p h_r i;
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
                   (ij ==> Veq.injective_on_dom #(Fin.fin (len f)) (L.index f)) /\
                   (forall (y : b) . L.mem (Some y) f ==> L.mem y rng)))
          (decreases f)
  = match f with
  | [] -> ()
  | None :: fs    ->
      let ij, rng = check_injective_on_dom_aux fs in
      check_injective_on_dom_aux_spec fs;
      if ij
      then Veq.injective_on_domI #(Fin.fin (len f)) (L.index f) (fun i i' ->
        assert (L.index f i  == L.index fs (i -1));
        assert (L.index f i' == L.index fs (i'-1)))
  | Some y :: fs ->
      let ij, rng = check_injective_on_dom_aux fs in
      check_injective_on_dom_aux_spec fs;
      if ij && not (L.mem y rng)
      then Veq.injective_on_domI #(Fin.fin (len f)) (L.index f) (fun i i' ->
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
                   Veq.injective_on_dom #(Fin.fin src_n) (L.index res)))
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
                        Veq.injective_on_domI #(Fin.fin src_n) (L.index res) (fun i j ->
                          if i > 0 && j > 0 then ()
                          else if i = 0 && j = 0 then ()
                          else false_elim ()
                        )
             | None   -> let res'  = build_injection_iter #(src_n-1) g mask in
                        let res   = None :: res'                            in
                        build_injection_iter_spec #(src_n-1) g mask;
                        Veq.injective_on_domI #(Fin.fin src_n) (L.index res) (fun i j ->
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
#push-options "--ifuel 0 --fuel 1 --z3rlimit 1000 --z3refresh"
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
          (ensures Veq.map_to_eq src trg (L.index ij)) (decreases ij)
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


(*** Building a [spec_find_ro] *)

#push-options "--fuel 2"
let rec ens_refl_impl_eqs
      (#pre #post : Vpl.vprop_list) (#sl0 : Vpl.sl_f pre) (#sl1 : Vpl.sl_f post)
      (#ens : Type0) (#es : list (sel_eq_t pre post))
      (r : ens_refl sl0 sl1 ens es)
      (e : sel_eq_t pre post)
  : Lemma (requires  L.memP e es /\ ens) (ensures sl0 e._1 == U.cast _ (sl1 e._2))
          (decreases r)
  = match r with
  | EnsEq e' p _ ->
          assert (e == e')
  | EnsConj #_ #_ #_ #_ #ens0 #ens1 #es0 #es1 r0 r1 ->
          Ll.append_memP e es0 es1;
          eliminate L.memP e es0 \/ L.memP e es1
            returns sl0 e._1 == U.cast _ (sl1 e._2)
               with _ . ens_refl_impl_eqs r0 e
                and _ . ens_refl_impl_eqs (r1 ()) e
#pop-options

#push-options "--ifuel 0"
let ograph_of_sl_eqs_spec
      (#pre #post : Vpl.vprop_list)
      (eqs : list (sel_eq_t pre post))
      (i_post : Ll.dom post) (i_pre : Ll.dom pre)
  : Lemma (L.index (L.index (ograph_of_sl_eqs eqs) i_post) i_pre <==>
            (L.index pre i_pre == L.index post i_post /\ L.mem (i_pre, i_post) eqs))
  =
    let n_pre  = L.length pre  in
    let n_post = L.length post in
    let g0 = Ll.repeat n_post (Ll.repeat n_pre false) in
    let f0 (i_pre : Ll.dom pre) (c : Ll.vec n_pre bool) : Ll.vec n_pre bool
      = Ll.set i_pre true c     in
    let f1 (g : ograph n_post n_pre) (e : sel_eq_t pre post) : ograph n_post n_pre
      = let i_pre, i_post = e in Ll.map_nth i_post (f0 i_pre) g
    in
    assert (ograph_of_sl_eqs eqs == L.fold_left f1 g0 eqs) by (trefl ());
    let p (eqs : list (sel_eq_t pre post)) (g : ograph n_post n_pre) : Type0 =
      L.index (L.index g i_post) i_pre <==>
         (L.index pre i_pre == L.index post i_post /\ L.mem (i_pre, i_post) eqs)
    in
    Ll.fold_left_ind f1 g0 eqs (fun eqs g _ -> p eqs g) (fun eqsl g e _ -> ());
    assert (p (L.rev eqs) (ograph_of_sl_eqs eqs));
    FStar.Classical.forall_intro (L.rev_mem eqs);
    assert (p eqs (ograph_of_sl_eqs eqs))
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let sel_eq_on_injection_iff_eq
      (#pre #post : Vpl.vprop_list)
      (f : Veq.partial_injection post pre)
      (sl0 : Vpl.sl_f pre) (sl1 : Vpl.sl_f post)
  : Lemma Vpl.(sel_eq_on (L.index f) sl0 sl1
            <==> extract_vars (Veq.ij_matched_equiv f) (filter_sl (Msk.mask_not (Veq.ij_trg_mask f)) sl0)
               == filter_sl (Msk.mask_not (Veq.ij_src_mask f)) sl1)
  = Vpl.(
    let m0 = Msk.mask_not (Veq.ij_trg_mask f) in
    let m1 = Msk.mask_not (Veq.ij_src_mask f) in
    let fsl0 = extract_vars (Veq.ij_matched_equiv f) (filter_sl m0 sl0) in
    let fsl1 = filter_sl m1 sl1                                         in
    introduce sel_eq_on (L.index f) sl0 sl1 ==> fsl0 == fsl1
      with _ . Fl.flist_extensionality fsl0 fsl1
      begin fun i1 ->
        let i = Msk.mask_pull m1 i1 in
        L.lemma_index_memP f i;
        let Some j = L.index f i    in
        let j1 = Msk.mask_push m0 j in
        calc (==) {
          (|_, fsl0 i1|) <: t : Type & t;
        == { }
          (|_, filter_sl m0 sl0 (Veq.ij_matched_equiv f i1)|);
        == { }
          (|_, filter_sl m0 sl0 j1|);
        == { }
          (|_, sl0 j|);
        == {(*by assumption*)}
          (|_, sl1 i|);
        == { }
          (|_, fsl1 i1|);
        }
      end;
    introduce fsl0 == fsl1 ==> sel_eq_on (L.index f) sl0 sl1
      with _ . introduce forall (i : Ll.dom post {Some? (L.index f i)}) .
                         sl0 (Some?.v (L.index f i)) == U.cast _ (sl1 i)
      with begin
        L.lemma_index_memP f i;
        let Some j = L.index f i    in
        let i1 = Msk.mask_push m1 i in
        let j1 = Msk.mask_push m0 j in
        calc (==) {
          (|_, sl1 i|) <: t : Type & t;
        == { }
          (|_, fsl1 i1|);
        == {(*by assumption*)}
          (|_, fsl0 i1|);
        == { }
          (|_, filter_sl m0 sl0 (Veq.ij_matched_equiv f i1)|);
        == { }
          (|_, filter_sl m0 sl0 j1|);
        == { }
          (|_, sl0 j|);
        }
      end
  )
#pop-options

// TODO:MOVE
#push-options "--fuel 0 --ifuel 0"
let pequiv_trans_sym #a (#l0 #l1 #l2 : list a) (f : Perm.pequiv l0 l1) ($g : Perm.pequiv l1 l2)
  : Lemma Perm.(pequiv_sym (pequiv_trans f g) == pequiv_trans (pequiv_sym g) (pequiv_sym f))
  =
    let rew1 () : Lemma (L.length l1 == L.length l0) = () in
    let rew2 () : Lemma (L.length l2 == L.length l0) = () in
    assert Perm.(eq2 #(perm_f (L.length l2))
                      (pequiv_sym (pequiv_trans f g)) (pequiv_trans (pequiv_sym g) (pequiv_sym f)))
      by (norm [delta_only [`%Perm.pequiv_sym; `%Perm.pequiv_trans; `%U.cast]; iota];
          l_to_r [(`(`@rew1)); (`(`@rew2))];
          with_policy Goal (fun () -> apply_lemma (`Perm.inv_f_comp));
          l_to_r [(`(`@rew1)); (`(`@rew2))])

let pequiv_append_sym #a (#l0 #l0' : list a) ($f0 : Perm.pequiv l0 l0')
                         (#l1 #l1' : list a) ($f1 : Perm.pequiv l1 l1')
  : Lemma Perm.(pequiv_sym (pequiv_append f0 f1) == pequiv_append (pequiv_sym f0) (pequiv_sym f1))
  =
    let rew0 () : Lemma L.(length l0' == length l0) = () in
    let rew1 () : Lemma L.(length l1' == length l1) = () in
    let rew2 () : Lemma L.(eq2 #nat (length (l0' @ l1')) (length l0 + length l1)) = () in
    let rew3 () : Lemma L.(eq2 #nat (length (l0  @ l1 )) (length l0 + length l1)) = () in
    assert Perm.(eq2 #(perm_f L.(length (l0' @ l1')))
                      (pequiv_sym (pequiv_append f0 f1)) (pequiv_append (pequiv_sym f0) (pequiv_sym f1)))
      by (norm [delta_only [`%Perm.pequiv_sym; `%Perm.pequiv_append; `%U.cast]; iota];
          l_to_r [(`(`@rew0)); (`(`@rew1)); (`(`@rew2)); (`(`@rew3))];
          apply_lemma (`Perm.perm_f_append_inv))

let pequiv_sym_sym #a (#l0 #l1 : list a) ($f : Perm.pequiv l0 l1)
  : Lemma Perm.(pequiv_sym (pequiv_sym f) == f)
  =
    let rew () : Lemma L.(length l1 == length l0) = () in
    assert Perm.(eq2 #(perm_f (L.length l0)) (pequiv_sym (pequiv_sym f)) f)
      by (norm [delta_only [`%Perm.pequiv_sym; `%U.cast]; iota];
          l_to_r [``@rew];
          apply_lemma (`Perm.inv_f_invol))

let extract_vars_index
      (#src #dst : Vpl.vprop_list) (p : Vpl.vequiv_perm src dst)
      (xs : Vpl.sl_f src) (i : Ll.dom dst)
  : Lemma (Vpl.extract_vars p xs i === xs (p i))
  = ()

let if_eq_else #a guard (thn els : a)
  : Lemma (requires not guard) (ensures (if guard then thn else els) == els)
  = ()

let append_vars_index_right (#v0 #v1 : Vpl.vprop_list) (sl0 : Vpl.sl_f v0) (sl1 : Vpl.sl_f v1)
                            (i : Fin.fin L.(length v1))
  : Lemma (Vpl.append_vars sl0 sl1 (L.length v0 + i) === sl1 i)
  = Ll.pat_append ()

#push-options "--z3rlimit 20"
let build_spec_find_ro_from_ij_lem1
      (pre post : Vpl.vprop_list) (ij : Veq.partial_injection post pre)
      (p0 : Vpl.vequiv_perm (Msk.filter_mask (Msk.mask_not (Veq.ij_trg_mask ij)) pre)
                            (Msk.filter_mask (Msk.mask_not (Veq.ij_src_mask ij)) post))
      (sl1    : Vpl.sl_f Msk.(filter_mask (Veq.ij_src_mask ij) post))
      (sl_fr1 : Vpl.sl_f Msk.(filter_mask (mask_not (Veq.ij_trg_mask ij)) pre))
  : Lemma Vpl.(extract_vars p0 sl_fr1
            == filter_sl (Msk.mask_not (Veq.ij_src_mask ij))
                  (extract_vars Perm.(pequiv_sym (pequiv_trans
                    (Msk.mask_pequiv_append (Veq.ij_src_mask ij) post)
                    (pequiv_append (pequiv_refl _) (pequiv_sym p0)))
                  ) (append_vars sl1 sl_fr1)))
  = Vpl.(
    let m0    = Msk.mask_not (Veq.ij_trg_mask ij) in
    let m1    = Msk.mask_not (Veq.ij_src_mask ij) in
    let m1'   = Veq.ij_src_mask ij                in
    let n1'   = Msk.mask_len m1'                  in
    let ro    = Msk.filter_mask m0  pre           in
    let ro'   = Msk.filter_mask m1  post          in
    let post' = Msk.filter_mask m1' post          in

    let p0   : vequiv_perm ro ro' = p0                                  in
    let p1a  = Msk.mask_pequiv_append m1' post                          in
    let p1b  = Perm.(pequiv_append (pequiv_refl post') (pequiv_sym p0)) in
    let p1   : Vpl.vequiv_perm post L.(post' @ ro)
             = Perm.(pequiv_trans p1a p1b)                              in
    let p1'a = Msk.mask_pequiv_append' m1' post                         in
    let p1'b = Perm.(pequiv_append (pequiv_refl post') p0)              in
    let p1' : Vpl.vequiv_perm L.(post' @ ro) post
            = Perm.(pequiv_trans p1'b p1'a)                             in

    U.assert_by (Perm.pequiv_sym p1 == p1') Perm.(fun () ->
      pequiv_trans_sym p1a p1b;
      pequiv_append_sym (pequiv_refl post') (pequiv_sym p0);
      Msk.mask_perm_append_inv m1'
    );

    let sl1'a = append_vars sl1 sl_fr1 in
    let sl1'  = extract_vars p1' sl1'a in
    Fl.flist_extensionality (extract_vars p0 sl_fr1) (filter_sl m1 sl1') (fun i1 ->
      let i0 = Msk.mask_pull m1 i1 in
      let i2 = n1' + i1            in
      let j1 = p0 i1               in
      assert (L.length post' == n1');
      calc (==) {
        (|_, filter_sl m1 sl1' i1|) <: t : Type & t;
      == { }
        (|_, sl1' i0|);
      == { }
        (|_, extract_vars p1' sl1'a i0|);
      == { extract_vars_index p1' sl1'a i0 }
        (|_, sl1'a (p1' i0)|);
      == { assert (p1' i0 == p1'b (p1'a i0));
           Msk.mask_perm_append'_index m1' i0;
           assert (p1'a i0 == i2) }
        (|_, sl1'a (p1'b i2)|);
      == { let rew () : Lemma (L.length (Msk.filter_mask m1' post) == n1') = () in
           assert (p1'b i2 == n1' + p0 i1)
             by (norm [delta_only [`%Perm.pequiv_append; `%Perm.perm_f_append; `%Perm.mk_perm_f;
                                   `%U.cast; `%FunctionalExtensionality.on];
                       iota];
                 l_to_r [``@rew];
                 clear_all ();
                 apply_lemma (`U.eq2_trans);
                   apply_lemma (`if_eq_else); smt ();
                 smt ()) }
        (|_, sl1'a (n1' + j1)|);
      == { }
        (|_, append_vars sl1 sl_fr1 (n1' + j1)|);
      == { append_vars_index_right sl1 sl_fr1 j1 }
        (|_, sl_fr1 j1|);
      == { extract_vars_index p0 sl_fr1 i1 }
        (|_, extract_vars p0 sl_fr1 i1|);
      }
    )
  )
#pop-options

#pop-options

(**) private let __end_build_spec_find_ro_from_ij = ()
