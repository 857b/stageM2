module Experiment.Steel.CondSolver

module L = FStar.List.Pure

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


(***** [build_injection] *)

let rec build_injection_find_spec (#trg_n : nat) (g mask : vec trg_n bool) (i : nat)
  : Lemma (requires Some? (build_injection_find g mask i))
          (ensures (let j = Some?.v (build_injection_find g mask i) - i in
                    j >= 0 /\ L.index g j /\ L.index mask j))
          (decreases trg_n)
  = match g, mask with
  | [], [] | true :: _, true :: _ -> ()
  | _ :: g, _ :: mask -> build_injection_find_spec #(trg_n-1) g mask (i+1)

let rec build_injection_iter_spec (#src_n #trg_n : nat) (g : ograph src_n trg_n) (mask : vec trg_n bool)
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
let rec list_to_matrix_index (#a : Type) (n0 n1 : nat) (l : vec (n0 * n1) a) (i : Fin.fin n0) (j : Fin.fin n1)
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


(***** mask *)

let rec merge_fun_on_mask_index #src_n mask #b f g (i : nat)
  : Lemma (requires i < src_n)
          (ensures  L.index (merge_fun_on_mask #src_n mask #b f g) i ==
                   (if L.index mask i then f i (mask_push #src_n mask i) else g i))
          [SMTPat (L.index (merge_fun_on_mask #src_n mask #b f g) i)]
  = match mask with
  | true  :: mask ->
          let f' (i : Fin.fin (src_n-1) {L.index mask i}) (j : Fin.fin (mask_len mask)) = f (i + 1) (j + 1) in
          let g' (i : Fin.fin (src_n-1) {not (L.index mask i)}) = g (i + 1) in
          assert (merge_fun_on_mask #src_n (true :: mask) f g ==
                  f 0 0 :: merge_fun_on_mask #(src_n-1) mask f' g')
              by (trefl ());
          if i > 0 then merge_fun_on_mask_index #(src_n-1) mask f' g' (i - 1)
  | false :: mask ->
          let f' (i : Fin.fin (src_n-1) {L.index mask i}) (j : Fin.fin (mask_len mask)) = f (i + 1) j in
          let g' (i : Fin.fin (src_n-1) {not (L.index mask i)}) = g (i + 1) in
          assert (merge_fun_on_mask #src_n (false :: mask) f g ==
                  g 0 :: merge_fun_on_mask #(src_n-1) mask f' g')
              by (trefl ());
          if i > 0 then merge_fun_on_mask_index #(src_n-1) mask f' g' (i - 1)

let rec mask_push_pull (#len : nat) (mask : vec len bool) (j : Fin.fin (mask_len mask))
  : Lemma (ensures mask_push mask (mask_pull mask j) = j) (decreases mask)
          [SMTPat (mask_push mask (mask_pull mask j))]
  = match mask with
  | true  :: mask -> if j = 0 then () else mask_push_pull #(len - 1) mask (j - 1)
  | false :: mask -> mask_push_pull #(len - 1) mask j

let rec mask_pull_push (#len : nat) (mask : vec len bool) (i : Fin.fin len {L.index mask i})
  : Lemma (ensures mask_pull mask (mask_push mask i) = i)
          [SMTPat (mask_pull mask (mask_push mask i))]
  = if i = 0 then ()
    else let b :: mask = mask in
         if b then mask_pull_push #(len-1) mask (i-1)
         else mask_pull_push #(len-1) mask  (i-1)

let rec filter_mask_push (#len : nat) (mask : vec len bool) (i : Fin.fin len {L.index mask i})
                         (#a : Type) (l : vec len a)
  : Lemma (ensures L.index (filter_mask mask l) (mask_push mask i) == L.index l i) (decreases l)
  = if i <> 0
    then let b :: mask = mask in
         let x :: xs   = l    in
         if b then filter_mask_push #(len-1) mask (i-1) xs
         else filter_mask_push #(len-1) mask (i - 1) xs


(***** [cond_sol] *)

let rec cond_sol_all_unmatched (#a : Type) (#src #trg : list a) (sl : cond_sol true src trg)
  : Lemma (ensures cond_sol_unmatched sl == []) (decreases sl)
  = match sl with
  | CSeq   _ _ -> ()
  | CSinj  _ _ _ _ sl -> cond_sol_all_unmatched sl

let rec cond_sol_unmatched_injective (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
  : Lemma (ensures Perm.injective (L.index (cond_sol_unmatched sl))) (decreases sl)
  = match sl with
  | CSeq  _ _ | CSnil _ -> ()
  | CSinj _ src trg ij sl' ->
          let um = cond_sol_unmatched sl' in
          let mask = ij_trg_mask ij       in
          Perm.injectiveI (L.index (cond_sol_unmatched sl)) (fun i i' ->
            // injectivity of mask_pull
            mask_push_pull mask (L.index um i );
            mask_push_pull mask (L.index um i');
            cond_sol_unmatched_injective sl')

#push-options "--z3rlimit 60"
let rec cond_sol_inj_unmatched
     (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg) (j : Fin.fin (len trg))
  : Lemma (ensures L.mem j (cond_sol_inj sl) <==> not (L.mem j (cond_sol_unmatched sl)))
          (decreases sl)
  = match sl with
  | CSeq _ l -> L.lemma_index_memP (cond_sol_inj sl) j
  | CSnil _  -> L.lemma_index_memP (cond_sol_unmatched sl) j
  | CSinj  _ src trg ij sl' ->
      let inj' = cond_sol_inj sl'    in
      let mask_src = ij_src_mask ij  in
      let mask_trg = ij_trg_mask ij  in
      let trg_fin = Fin.fin (len trg) in
      let um : list (Fin.fin (mask_len mask_trg)) = cond_sol_unmatched sl' in
      if L.mem (Some j) ij
      then begin
        let i = Ll.mem_findi (Some j) ij in
        L.lemma_index_memP (cond_sol_inj sl) i;
        assert (L.mem j (cond_sol_inj sl));
        L.memP_map_elim #(Fin.fin (mask_len mask_trg)) #(Fin.fin (len trg))
                        (mask_pull mask_trg) j um
      end else begin
        let j' = mask_push mask_trg j in
        introduce L.mem j (cond_sol_inj sl) ==> L.mem j' inj'
          with _ . begin
            let i = Ll.mem_findi j (cond_sol_inj sl) in
            if L.index mask_src i
            then begin
              assert (mask_pull mask_trg (L.index inj' (mask_push mask_src i)) == j);
              mask_push_pull mask_trg (L.index inj' (mask_push mask_src i));
              assert (L.index inj' (mask_push mask_src i) == j');
              L.lemma_index_memP inj' (mask_push mask_src i)
            end else begin
              assert (L.index ij i = Some j);
              L.lemma_index_memP ij i;
              false_elim ()
            end
          end;
        introduce L.mem j' inj' ==> L.mem j (cond_sol_inj sl)
          with _ . begin
            let i' = Ll.mem_findi j' inj' in
            mask_push_pull mask_src i';
            L.lemma_index_memP (cond_sol_inj sl) (mask_pull mask_src i')
          end;
        calc (<==>) {
          L.memP j (cond_sol_inj sl);
        <==> { }
          L.memP j' inj';
        <==> { cond_sol_inj_unmatched sl' j' }
          ~ (L.mem j' um);
        <==> { mask_pull_push mask_trg j;
            L.memP_map_intro #_ #trg_fin (mask_pull mask_trg) j' um;
            L.memP_map_elim  #_ #trg_fin (mask_pull mask_trg) j  um }
          ~ (L.memP j (L.map #_ #trg_fin (mask_pull mask_trg) um));
        <==> { }
          ~ (L.mem j (cond_sol_unmatched sl));
        }
      end
#pop-options

// The verification time is unstable
#push-options "--z3rlimit 60"
let rec cond_sol_inj_injective (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
      (i i' : Fin.fin (len src))
  : Lemma (requires L.index (cond_sol_inj sl) i = L.index (cond_sol_inj sl) i')
          (ensures i = i')
          (decreases sl)
  = match sl with
  | CSeq  _ _ | CSnil _ -> ()
  | CSinj all src trg ij sl' ->
      let inj' = cond_sol_inj sl'         in
      let mask_src = ij_src_mask ij       in
      let mask_trg = ij_trg_mask ij       in
      let y = L.index (cond_sol_inj sl) i in
      match L.index mask_src i, L.index mask_src i' with
      | true,  true  -> // by injectivity of inj'
          assert (y = mask_pull mask_trg (L.index inj' (mask_push mask_src i)));
          //injectivity of [mask_pull mask_trg]
          mask_push_pull mask_trg (L.index inj' (mask_push mask_src i));
          mask_push_pull mask_trg (L.index inj' (mask_push mask_src i'));
          cond_sol_inj_injective sl' (mask_push mask_src i) (mask_push mask_src i');
          //injectivity of [mask_push mask_src]
          mask_pull_push mask_src i;
          mask_pull_push mask_src i'
      | false, false -> // by injectivity of ij
         assert (y = Some?.v (L.index ij i))
      | true,  false -> // we have both [L.index mask_trg y] and its negation
         U.assert_by (L.index mask_trg y) (fun () ->
           assert (y = mask_pull mask_trg (L.index inj' (mask_push mask_src i))));
         U.assert_by (not (L.index mask_trg y)) (fun () ->
           assert (y = Some?.v (L.index ij i'));
           assert (L.index ij i' = Some y);
           L.lemma_index_memP ij i';
           assert (L.mem (Some y) ij));
         false_elim ()
      | false, true  -> L.lemma_index_memP ij i
#pop-options

#push-options "--z3rlimit 20"
let rec cond_sol_inj_eq (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
      (i : Fin.fin (len src))
  : Lemma (ensures L.index trg (L.index (cond_sol_inj sl) i) == L.index src i)
          (decreases sl)
  = match sl with
  | CSeq  _ _ | CSnil _ -> ()
  | CSinj all src trg ij sl' ->
          let inj' = cond_sol_inj sl'         in
          let mask_src = ij_src_mask ij       in
          let mask_trg = ij_trg_mask ij       in
          let y = L.index (cond_sol_inj sl) i in
          if L.index mask_src i
          then begin
            let i' = mask_push mask_src i in
            assert (y = mask_pull mask_trg (L.index inj' i'));
            calc (==) {
              L.index trg y;
            == { mask_push_pull mask_trg (L.index inj' i');
                 filter_mask_push mask_trg y trg }
              L.index (filter_mask mask_trg trg) (L.index inj' i');
            == { cond_sol_inj_eq sl' i' }
              L.index (filter_mask mask_src src) i';
            == { filter_mask_push mask_src i src }
              L.index src i;
            }
          end
#pop-options


#push-options "--z3rlimit 30"
let cond_sol_bij_spec (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
  : Lemma (len src + len (cond_sol_unmatched sl) = len trg /\
           Perm.injective (cond_sol_bij sl) /\
           L.(src @ cond_sol_unmatched_v sl) == Perm.apply_perm_r (Perm.mk_perm_f (len trg) (cond_sol_bij sl)) trg)
  =
    let src_l = len src               in
    let trg_l = len trg               in
    let ij    = cond_sol_inj sl       in
    let um    = cond_sol_unmatched sl in
    let um_l  = len um                in
    let f     = cond_sol_bij sl       in
    
    Perm.injectiveI #(Fin.fin (src_l + um_l)) f (fun i i' ->
      let j = cond_sol_bij sl i in
      match (i < src_l), (i' < src_l) with
      | true,  true  -> cond_sol_inj_injective sl i i'
      | false, false -> cond_sol_unmatched_injective sl
      | true,  false -> L.lemma_index_memP ij i;
                       L.lemma_index_memP um (i' - src_l);
                       cond_sol_inj_unmatched sl j
      | false, true  -> L.lemma_index_memP ij i';
                       L.lemma_index_memP um (i - src_l);
                       cond_sol_inj_unmatched sl j);
    
    Perm.surjectiveI #(Fin.fin (src_l + um_l)) #(Fin.fin trg_l) f
      (fun j -> if L.mem j ij
             then Ll.mem_findi j ij
             else (
               cond_sol_inj_unmatched sl j;
               src_l + Ll.mem_findi j um
             ));

    Perm.fin_injective_le  (src_l + um_l) trg_l f;
    Perm.fin_surjective_ge (src_l + um_l) trg_l f;
    
    Ll.list_extensionality L.(src @ cond_sol_unmatched_v sl)
                           (Perm.apply_perm_r (Perm.mk_perm_f (len trg) (cond_sol_bij sl)) trg)
    begin fun (i : Fin.fin (src_l + um_l)) ->
      Ll.append_index src (cond_sol_unmatched_v sl) i;
      if i < src_l then cond_sol_inj_eq sl i
    end
#pop-options
