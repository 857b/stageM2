module Experiment.Steel.Tac

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
