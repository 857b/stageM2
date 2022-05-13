module Experiment.Steel.CondSolver

module M    = Experiment.Steel.Repr.M
module U    = Learn.Util
module L    = FStar.List.Pure
module Ll   = Learn.List
module Fin  = FStar.Fin
module Perm = Learn.Permutation

open FStar.Tactics
open Learn.Tactics.Util
open FStar.Mul

(***** [truth_refl] *)

noeq
type truth_refl : prop -> bool -> Type =
  | ReflTrue  : truth_refl True true
  | ReflFalse : (p : prop) -> truth_refl p false

let term_eq_true (p : term) : Tac bool =
  match p with
  | Tv_FVar fv -> implode_qn (inspect_fv fv) = (`%Prims.l_True)
  | _ -> false


let mk_truth_refl (p : term) : Tac (bool & binder) =
  let b = fresh_uvar (Some (`bool)) in
  let bd, res = build (`truth_refl (`#p) (`#b)) (fun () ->
    norm [iota; primops; simplify];
    let _, args = collect_app (cur_goal ()) in
    if L.length args <> 2 then fail "expected a truth_refl";
    let p' = (L.index args 0)._1 in
    if term_eq_true p'
    then (apply (`ReflTrue); true)
    else (apply (`(ReflFalse)); false))
  in
  res, bd


(*let _ =
  assert True
    by (let b,_ = mk_truth_refl (`(1 == 1)) in fail (term_to_string (quote b)))*)

(* TODO? convert to for_all2P *)
noeq
type truth_refl_list : list prop -> list bool -> Type =
  | ReflLNil   : truth_refl_list [] []
  | ReflLTrue  : (#ps : list prop) -> (#bs : list bool) ->
                 truth_refl_list ps bs -> truth_refl_list (True :: ps) (true :: bs)
  | ReflLFalse : (p0 : prop) -> (#ps : list prop) -> (#bs : list bool) ->
                 truth_refl_list ps bs -> truth_refl_list (p0 :: ps) (false :: bs)

val truth_refl_list_length (#ps : list prop) (#bs : list bool) (rfl : truth_refl_list ps bs)
  : Lemma (L.length ps = L.length bs)

val truth_refl_list_index (#ps : list prop) (#bs : list bool) (rfl : truth_refl_list ps bs)
                              (i : Fin.fin (L.length bs))
  : Lemma (requires L.index bs i) (ensures L.length ps = L.length bs /\ L.index ps i)

(* FIXME? this generate an additional smt goal *)
let mk_truth_refl_list_goal () : Tac (list bool) =
  norm [iota; primops; simplify];
  repeatb (fun () ->
    try (apply (`ReflLNil); None)
    with | _ -> try (apply (`ReflLTrue); Some true)
    with | _ -> try (apply (`ReflLFalse); Some false)
    with | _ -> fail "mk_truth_refl_list")

let mk_truth_refl_list (ps : term) : Tac (list bool & term & binder) =
  let bs = fresh_uvar (Some (`(list bool))) in
  let bd, res = build (`truth_refl_list (`#ps) (`#bs)) mk_truth_refl_list_goal
  in res, bs, bd

(*let _ =
  assert True
    by (let bs,_,_ = mk_truth_refl_list (`[(1 == 1); (1 == 2); (2 + 2 == 4)]) in
        fail (term_to_string (quote bs)))*)


(*** Building an injection *)

let len (#a : Type) : list a -> nat = L.length #a
type vec (n : nat) (a : Type) = l : list a {len l = n}

/// Graph over-approximation
type ograph (src_n : nat) (trg_n : nat) = vec src_n (vec trg_n bool)

let injective_on_dom (#a #b : Type) (f : a -> option b) : prop =
  forall (x x' : a) . Some? (f x) /\ f x == f x' ==> x == x'

let injective_on_domI (#a #b : Type) (f : a -> option b)
                      (prf : (x : a) -> (x' : a) -> Lemma (requires Some? (f x) /\ f x == f x') (ensures x == x'))
  : Lemma (injective_on_dom f)
  = FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 prf)

let rec build_injection_find (#trg_n : nat) (g mask : vec trg_n bool) (i : nat)
  : Tot (option (Fin.fin (i + trg_n))) (decreases trg_n)
  = match g, mask with
  |   [],       []    -> None
  | true :: _, true :: _ -> Some i
  | _ :: g,    _ :: mask -> build_injection_find #(trg_n-1) g mask (i+1)

let rec build_injection_iter (#src_n #trg_n : nat) (g : ograph src_n trg_n) (mask : vec trg_n bool)
  : Tot (vec src_n (option (Fin.fin trg_n))) (decreases src_n)
  = match g with
  | [] -> []
  | g0 :: g -> let y = build_injection_find g0 mask 0 in
             let mask' = match y with
                         | Some y -> Ll.set y false mask
                         | None   -> mask
             in y :: build_injection_iter #(src_n-1) g mask'

let build_injection (#src_n #trg_n : nat) (g : ograph src_n trg_n)
  : Tot (vec src_n (option (Fin.fin trg_n)))
  = build_injection_iter g (Ll.initi 0 trg_n (fun _ -> true))


val build_injection_find_spec (#trg_n : nat) (g mask : vec trg_n bool) (i : nat)
  : Lemma (requires Some? (build_injection_find g mask i))
          (ensures (let j = Some?.v (build_injection_find g mask i) - i in
                    j >= 0 /\ L.index g j /\ L.index mask j))

val build_injection_iter_spec (#src_n #trg_n : nat) (g : ograph src_n trg_n) (mask : vec trg_n bool)
  : Lemma (ensures (let res = build_injection_iter g mask in
                   (forall (i : Fin.fin src_n) . {:pattern (L.index res i)}
                      Some? (L.index res i) ==> (L.index (L.index g i) (Some?.v (L.index res i))
                                            && L.index mask (Some?.v (L.index res i)))) /\
                   injective_on_dom #(Fin.fin src_n) (L.index res)))

let build_injection_spec (#src_n #trg_n : nat) (g : ograph src_n trg_n)
  : Lemma (let res = build_injection g in
          (forall (i : Fin.fin src_n) . {:pattern (L.index res i)}
             Some? (L.index res i) ==> L.index (L.index g i) (Some?.v (L.index res i))) /\
          injective_on_dom #(Fin.fin src_n) (L.index res))
  = build_injection_iter_spec g (Ll.initi 0 trg_n (fun _ -> true))


/// The type of partial injection between equal elements of two lists.
/// In practice [a] is [vprop']
type partial_injection (#a : Type) (src trg : list a) =
  f : vec (len src) (option (Fin.fin (len trg))) {
    (forall (i : Fin.fin (len src)) . Some? (L.index f i) ==>
         L.index trg (Some?.v (L.index f i)) == L.index src i) /\
    injective_on_dom #(Fin.fin (len src)) (L.index f)
  }


let list_of_equalities (#a : Type) (src trg : list a) : list prop =
  L.flatten (L.map (fun x -> L.map #_ #prop (fun y -> (x == y)) trg) src)

val list_of_equalities_length (#a : Type) (src trg : list a)
  : Lemma (len (list_of_equalities src trg) = len src * len trg)
          [SMTPat (L.length (list_of_equalities src trg))]

val list_of_equalities_index (#a : Type) (src trg : list a) (i : Fin.fin (len src)) (j : Fin.fin (len trg))
  : Lemma (i * len trg + j < len (list_of_equalities src trg) /\
           L.index (list_of_equalities src trg) (i * len trg + j) == (L.index src i == L.index trg j))


let rec list_to_matrix (#a : Type) (n0 n1 : nat) (l : vec (n0 * n1) a)
  : Tot (vec n0 (vec n1 a)) (decreases n0)
  = if n0 = 0 then []
    else let l0, ls = L.splitAt n1 l in
         (**) L.splitAt_length n1 l;
         l0 :: list_to_matrix(n0 - 1) n1 ls

val list_to_matrix_index (#a : Type) (n0 n1 : nat) (l : vec (n0 * n1) a) (i : Fin.fin n0) (j : Fin.fin n1)
  : Lemma (i * n1 + j < n0 * n1 /\
           L.index (L.index (list_to_matrix n0 n1 l) i) j == L.index l (i * n1 + j))
          [SMTPat (L.index (L.index (list_to_matrix n0 n1 l) i) j)]


let ograph_of_equalities (#a : Type) (src trg : list a) (bs : list bool)
      (rfl : truth_refl_list (list_of_equalities src trg) bs)
  : ograph (len src) (len trg)
  = 
    (**) truth_refl_list_length rfl;
    list_to_matrix (L.length src) (L.length trg) bs

val ograph_of_equalities_index (#a : Type) (src trg : list a) (bs : list bool)
      (rfl : truth_refl_list (list_of_equalities src trg) bs)
      (i : Fin.fin (len src)) (j : Fin.fin (len trg))
  : Lemma (requires L.index (L.index (ograph_of_equalities src trg bs rfl) i) j)
          (ensures  L.index src i == L.index trg j)


let build_partial_injection (#a : Type) (src trg : list a) (bs : list bool)
      (rfl : truth_refl_list (list_of_equalities src trg) bs)
  : partial_injection src trg
  =
    let g = ograph_of_equalities src trg bs rfl in
    (**) FStar.Classical.forall_intro_2
    (**)   (FStar.Classical.move_requires_2 (ograph_of_equalities_index src trg bs rfl));
    (**) build_injection_spec g;
    build_injection g

let print_util (#a : Type) (x : a) : prop = True

let normal_list_of_equalities : list norm_step = [
  delta_only [`%list_of_equalities; `%L.flatten; `%L.map; `%L.op_At; `%L.append];
  iota; zeta]

let normal_build_partial_injection : list norm_step = [
  delta_only [`%build_partial_injection; `%ograph_of_equalities; `%list_to_matrix; `%L.splitAt;
              `%L.length; `%Ll.initi; `%len; `%Ll.set;
              `%build_injection; `%build_injection_iter; `%build_injection_find];
  iota; zeta; primops]

/// solves a goal of the form [partial_injection src dst]
let build_partial_injection_tac () : Tac unit =
  apply (`build_partial_injection);
  norm normal_list_of_equalities;
  let _ = mk_truth_refl_list_goal () in
  ()


(*let test_inj : partial_injection ['a';'b';'c';'a';'b'] ['a';'c';'b';'d';'e';'a'] =
  _ by (build_partial_injection_tac ())

let _ = assert (U.print_util test_inj)
            by (norm [delta_only [`%test_inj]];
                norm normal_build_partial_injection;
                fail "print")*)

(*let _ : partial_injection ['a';'b';'c';'a';'b'] ['a';'c';'b';'d';'e';'a'] =
  _ by (let goal = cur_goal () in
        let inj, () = build_term goal build_partial_injection_tac in
        exact inj)*)


(*** Unification condition solution *)

(** mask *)

let mask_len (mask : list bool) : nat =
  L.count true mask

let rec filter_mask (#a : Type) (#len : nat) (mask : vec len bool) (l : vec len a)
  : Tot (vec (mask_len mask) a) (decreases l)
  = match mask, l with
  | [], [] -> []
  | true  :: mask, x :: xs -> x :: filter_mask #a #(len-1) mask xs
  | false :: mask, _ :: xs -> filter_mask #a #(len-1) mask xs

let rec mask_push (#len : nat) (mask : vec len bool) (i : Fin.fin len {L.index mask i})
  : Tot (Fin.fin (mask_len mask))
  =
    if i = 0 then 0
    else let b :: mask = mask in
         if b then 1 + mask_push #(len-1) mask (i-1)
         else mask_push #(len-1) mask (i - 1)

let rec mask_pull (#len : nat) (mask : vec len bool) (j : Fin.fin (mask_len mask))
  : Tot (i : Fin.fin len {L.index mask i}) (decreases mask)
  = match mask with
  | true  :: mask -> if j = 0 then 0 else 1 + mask_pull #(len - 1) mask (j - 1)
  | false :: mask -> 1 + mask_pull #(len - 1) mask j

(* TODO? optimize *)
let rec merge_fun_on_mask (#src_n : nat) (mask : vec src_n bool) (#b : Type)
      (f : (i : Fin.fin src_n {L.index mask i}) -> (j : Fin.fin (mask_len mask)) -> b)
      (g : (i : Fin.fin src_n {not (L.index mask i)}) -> b)
  : Tot (vec src_n b) (decreases mask)
  = match mask with
  | [] -> []
  | true  :: mask -> f 0 0 :: merge_fun_on_mask #(src_n-1) mask (fun i j -> f (i+1) (j+1)) (fun i -> g (i+1))
  | false :: mask -> g 0   :: merge_fun_on_mask #(src_n-1) mask (fun i j -> f (i+1)   j  ) (fun i -> g (i+1))


val merge_fun_on_mask_index (#src_n : nat) (mask : vec src_n bool) (#b : Type)
      (f : (i : Fin.fin src_n {L.index mask i}) -> (j : Fin.fin (mask_len mask)) -> b)
      (g : (i : Fin.fin src_n {not (L.index mask i)}) -> b) (i : nat)
  : Lemma (requires i < src_n)
          (ensures  L.index (merge_fun_on_mask #src_n mask #b f g) i ==
                   (if L.index mask i then f i (mask_push #src_n mask i) else g i))
          [SMTPat (L.index (merge_fun_on_mask #src_n mask #b f g) i)]

val mask_push_pull (#len : nat) (mask : vec len bool) (j : Fin.fin (mask_len mask))
  : Lemma (mask_push mask (mask_pull mask j) = j)
          [SMTPat (mask_push mask (mask_pull mask j))]

val mask_pull_push (#len : nat) (mask : vec len bool) (i : Fin.fin len {L.index mask i})
  : Lemma (mask_pull mask (mask_push mask i) = i)
          [SMTPat (mask_pull mask (mask_push mask i))]

val filter_mask_push (#len : nat) (mask : vec len bool) (i : Fin.fin len {L.index mask i})
                     (#a : Type) (l : vec len a)
  : Lemma (L.index (filter_mask mask l) (mask_push mask i) == L.index l i)


/// Masks to select the elements that have *not* been matched

let ij_src_mask (#src_n : nat) (#b : Type) (ij : vec src_n (option b)) : vec src_n bool
  = L.map None? ij

let ij_trg_mask (#src_n #trg_n : nat) (ij : vec src_n (option (Fin.fin trg_n))) : vec trg_n bool
  = Ll.initi 0 trg_n (fun j -> not (L.mem (Some j) ij))


/// [cond_sol all src trg] represents the building of an injection from [src] to [trg].
/// In practice [trg] is the list of [vprop'] in the state before [src].
/// If [all] is set, the injection must be surjective, otherwise [src] needs to be completed with [cond_sol_unmatched]
/// in order to obtain a permutation.
noeq
type cond_sol (#a : Type) : (all : bool) -> list a -> list a -> Type =
  | CSeq  : (all : bool) -> (l : list a) -> cond_sol all l l
  | CSnil : (trg : list a) -> cond_sol false [] trg
  | CSinj : (all : bool) -> (src : list a) -> (trg : list a) -> (ij : partial_injection src trg) ->
            cond_sol all (filter_mask (ij_src_mask ij) src) (filter_mask (ij_trg_mask ij) trg) ->
            cond_sol all src trg

// ALT? define with cond_sol_inj
/// [cond_sol_unmatched sl] is the subset of indices of the target that have not been matched.
let rec cond_sol_unmatched (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
  : Tot (list (Fin.fin (len trg))) (decreases sl)
  = match sl with
  | CSeq  _ _ -> []
  | CSnil trg -> Ll.initi 0 (len trg) id
  | CSinj _ src trg ij sl ->
                let um = cond_sol_unmatched sl in
                let mask = ij_trg_mask ij      in
                L.map #_ #(Fin.fin (len trg)) (mask_pull mask) um

let cond_sol_unmatched_v (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
  : list a
  = L.map (L.index trg) (cond_sol_unmatched sl)

let rec cond_sol_inj (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
  : Tot (vec (len src) (Fin.fin (len trg))) (decreases sl)
  = match sl with
  | CSeq  _ l -> Ll.initi 0 (len l) id
  | CSnil _   -> []
  | CSinj all src trg ij sl ->
                let inj' = cond_sol_inj sl    in
                let mask_src = ij_src_mask ij in
                let mask_trg = ij_trg_mask ij in
                merge_fun_on_mask mask_src #(Fin.fin (len trg))
                  (fun _ j -> mask_pull mask_trg (L.index inj' j))
                  (fun i   -> Some?.v (L.index ij i))

let cond_sol_bij (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
  : Fin.fin (len src + len (cond_sol_unmatched sl)) -> Fin.fin (len trg)
  = 
    let src_l = len src               in
    let ij    = cond_sol_inj sl       in
    let um    = cond_sol_unmatched sl in
    fun i -> if i < src_l then L.index ij i else L.index um (i - src_l)


val cond_sol_all_unmatched (#a : Type) (#src #trg : list a) (sl : cond_sol true src trg)
  : Lemma (cond_sol_unmatched sl == [])

val cond_sol_unmatched_injective (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
  : Lemma (Perm.injective (L.index (cond_sol_unmatched sl)))

val cond_sol_inj_unmatched
      (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg) (j : Fin.fin (len trg))
  : Lemma (L.mem j (cond_sol_inj sl) <==> not (L.mem j (cond_sol_unmatched sl)))

val cond_sol_inj_injective (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
      (i i' : Fin.fin (len src))
  : Lemma (requires L.index (cond_sol_inj sl) i = L.index (cond_sol_inj sl) i')
          (ensures i = i')

val cond_sol_inj_eq (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
      (i : Fin.fin (len src))
  : Lemma (L.index trg (L.index (cond_sol_inj sl) i) == L.index src i)

val cond_sol_bij_spec (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
  : Lemma (len src + len (cond_sol_unmatched sl) = len trg /\
           Perm.injective (cond_sol_bij sl) /\
           L.(src @ cond_sol_unmatched_v sl) == Perm.apply_perm_r (Perm.mk_perm_f (len trg) (cond_sol_bij sl)) trg)


let cond_sol_to_equiv (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
  : Tot (Perm.pequiv trg L.(src @ cond_sol_unmatched_v sl))
  =
    (**) cond_sol_bij_spec sl;
    Perm.mk_perm_f (len trg) (cond_sol_bij sl)

let cond_sol_all_to_equiv (#a : Type) (#src #trg : list a) (sl : cond_sol true src trg)
  : Tot (Perm.pequiv trg src)
  =
    (**) cond_sol_all_unmatched sl;
    cond_sol_to_equiv sl


let normal_ij_mask : list norm_step = [
  delta_only [`%filter_mask; `%ij_src_mask; `%ij_trg_mask; `%L.map;
              `%None?; `%Ll.initi; `%op_Negation; `%L.mem];
  iota; zeta; primops]

/// This tactics solves a goal of the form [cond_sol all src trg]
let build_cond_sol (all : bool) : Tac unit
  = try if all then apply (`CSeq) else apply (`CSnil)
    with | _ ->
      apply_raw (`CSinj);
      build_partial_injection_tac ();
      norm normal_build_partial_injection;
      norm normal_ij_mask;
    try if all then apply (`CSeq) else apply (`CSnil)
    with | _ -> fail "build_cond_sol"

// TODO
let normal_cond_sol_to_equiv : list norm_step = [
    delta_only [`%cond_sol_to_equiv; `%cond_sol_bij; `%len; `%L.length; `%L.index];
    iota; zeta; primops
  ]

(*let test_cond_sol : cond_sol false ['a';'b';'c';'a'] ['a';'c';'b';'d';'e';'a'] =
  _ by (build_cond_sol false)    

let _ = assert (U.print_util (cond_sol_to_equiv (test_cond_sol)))
            by (norm [delta_only [`%test_cond_sol]];
                norm normal_build_partial_injection;
                norm normal_cond_sol_to_equiv;
                fail "print")*)

(*** Building [M.tree_cond] *)

// TODO: comment; generate shape; exceptions

open Steel.Effect.Common

/// u : uvar
/// p : post


// TODO
let norm_cond_sol () : Tac unit =
  norm normal_build_partial_injection;
  norm [delta_only [`%cond_sol_unmatched_v; `%cond_sol_unmatched;
                    `%len; `%L.length; `%Ll.initi];
        delta_qualifier ["unfold"];
        iota; zeta; primops];
  norm normal_ij_mask;
  norm [delta_only [`%L.index; `%mask_pull; `%L.hd; `%L.tl; `%L.tail; `%L.op_At; `%L.append];
        delta_qualifier ["unfold"];
        iota; zeta; primops]


let __build_TCspec_u
      (#a : Type) (#pre : M.pre_t) (#post : M.post_t a) (#req : M.req_t pre) (#ens : M.ens_t pre a post)
      (#pre' : M.pre_t)
      (cs0 : cond_sol false pre pre')
  : M.tree_cond (M.Tspec a pre post req ens) pre' (fun (x : a) -> L.(post x @ cond_sol_unmatched_v cs0))
  =
    let frame = cond_sol_unmatched_v cs0 in
    M.TCspec pre' (fun x -> L.(post x @ frame)) frame
             (cond_sol_to_equiv cs0)
             (fun x -> Perm.id_n (len L.(post x @ frame)))

let __build_TCspec_p
      (#a : Type) (#pre : M.pre_t) (#post : M.post_t a) (#req : M.req_t pre) (#ens : M.ens_t pre a post)
      (#pre' : M.pre_t) (#post' : M.post_t a)
      (cs0 : cond_sol false pre pre')
      (cs1 : (x : a) -> cond_sol true (post' x) L.(post x @ cond_sol_unmatched_v cs0))
  : M.tree_cond (M.Tspec a pre post req ens) pre' post'
  =
    M.TCspec pre' post' (cond_sol_unmatched_v cs0)
             (cond_sol_to_equiv cs0) (fun x -> cond_sol_all_to_equiv (cs1 x))


let __build_TCret_u
      (#a : Type) (#x : a)
      (#pre : M.pre_t)
  : M.tree_cond (M.Tret a x) pre (fun _ -> pre)
  =
    M.TCret pre (fun _ -> pre) (Perm.id_n (len pre))

let __build_TCret_p
      (#a : Type) (#x : a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (cs : cond_sol true (post x) pre)
  : M.tree_cond (M.Tret a x) pre post
  =
    M.TCret #a #x pre post (cond_sol_all_to_equiv cs)

let __defer_post_unification
      (#a : Type) (#t : M.prog_tree a) (#pre : M.pre_t) (#post0 : M.post_t a)
      (post1 : M.post_t a)
      (cd : M.tree_cond t pre post1)
      (_ : squash (post0 == post1))
  : M.tree_cond t pre post0
  = cd


let build_TCspec (post : bool) : Tac unit
  = if post then begin
      apply_raw (`(__build_TCspec_p));
      build_cond_sol false;
      norm_cond_sol ();
      let x = intro () in
      build_cond_sol true
    end else begin
      // FIXME : why apply_raw shelves sl ?
      let sl = fresh_uvar None in
      apply_raw (`(__build_TCspec_u (`#sl)));
      unshelve sl;
      build_cond_sol false
    end

let build_TCret (post : bool) : Tac unit
  = if post then begin
       apply_raw (`__build_TCret_p);
       build_cond_sol true
    end else
      apply_raw (`__build_TCret_u)

let rec build_TCbind (post : bool) : Tac unit
  = apply (`M.TCbind);
    // f
    build_tree_cond false;
    let x = intro () in
    norm_cond_sol ();
    // g
    if post then
      build_tree_cond true
    else begin
      // If post is false, the post is an uvar [post0] independent of [x].
      // The inferred post of [g] can depend (but should not) on [x].
      // Since we may need to normalize the inferred post in order to see that it does not depends on [x],
      // we introduce a fresh uvar [post1] that can depends on [x] and then prove that we can chose it for
      // the post [post0] of the bind.
      let post1 = fresh_uvar None in
      apply_raw (`(__defer_post_unification (`#post1)));
      build_tree_cond false;
      trefl () // [post0] <- [post1]
    end

and build_tree_cond (post : bool) : Tac unit
  =
    let goal = cur_goal () in
    let args = (collect_app goal)._2 in
    if L.length args < 4
    then fail "goal is not a tree_cond"
    else let hd = (collect_app (L.index args 1)._1)._1 in
    match inspect hd with
    | Tv_FVar fv ->
        // TODO? better solution to match
        let nd = inspect_fv fv in
        if Nil? nd then fail "empty fv";
        begin match L.last nd with
        | "Tspec"  -> build_TCspec post
        | "Tret"   -> build_TCret  post
        | "Tbind"  -> build_TCbind post
        | "TbindP" -> fail "TODO"
        | _ -> fail ("build_tree_cond: head is "^(implode_qn nd))
        end
    | _ -> fail ("build_tree_cond: head is "^term_to_string hd)


let _test_TCspec_u (v0 v1 : vprop') : squash True =
  _ by (let post' = fresh_uvar (Some (`(M.post_t int))) in
        let _,() =
          build (`(M.tree_cond
            (M.Tspec int [(`@v0)] (fun _ -> [(`@v1)]) (fun _ -> True) (fun _ _ _ -> True))
            [(`@v0)] (`#post')))
          (fun () -> build_TCspec false)
        in ())

let _test_TCspec_p (v0 v1 v2 : vprop') (vx : int -> vprop')
  : M.tree_cond (M.Tspec int [v0; v1] (fun x -> [v0; vx x]) (fun _ -> True) (fun _ _ _ -> True))
                ([v0; v1; v2]) (fun x -> [v2; vx x; v0])
  = _ by (build_TCspec true)


let _test_TCret_u (v0 v1 : vprop') : squash True =
  _ by (let post' = fresh_uvar (Some (`(M.post_t int))) in
        let _,() =
          build (`(M.tree_cond (M.Tret int 42) [(`@v0); (`@v1)] (`#post')))
          (fun () -> build_TCret false)
        in ())

let _test_TCret_p (v0 : vprop') (vx0 vx1 : int -> vprop')
  : M.tree_cond (M.Tret int 42)
                ([v0; vx0 42; vx1 42]) (fun x -> [v0; vx1 x; vx0 42])
  = _ by (build_TCret true)


let _test_TCbind_u (v0 v1 : vprop') (vx0 : int -> vprop') : squash True =
  _ by (let post' = fresh_uvar (Some (`(M.post_t int))) in
        let _,() =
          build (`(M.tree_cond
            (M.Tbind int int (M.Tspec int []          (fun x -> [(`@vx0) x]) (fun _ -> True) (fun _ _ _ -> True))
                   (fun x -> M.Tspec int [(`@vx0) x] (fun _ -> [(`@v1)])    (fun _ -> True) (fun _ _ _ -> True)))
            [(`@v0)] (`#post')))
          (fun () ->
            apply (`M.TCbind);
            build_TCspec false;
            let x = intro () in
            norm_cond_sol ();
            let post1 = fresh_uvar None in
            apply_raw (`(__defer_post_unification (`#post1)));
            build_TCspec false;
            norm_cond_sol ();
            trefl ()
          )
        in ())

let _test_TCbind_p (v0 v1 : vprop') (vx0 vx1 : int -> vprop')
  : M.tree_cond
        (M.Tbind int int (M.Tspec int []      (fun x -> [vx0 x])     (fun _ -> True) (fun _ _ _ -> True))
               (fun x -> M.Tspec int [vx0 x] (fun y -> [v1; vx1 y]) (fun _ -> True) (fun _ _ _ -> True)))
            [v0] (fun y -> [v0; vx1 y; v1])
  = _ by (
    apply (`M.TCbind);
    build_TCspec false;
    let x = intro () in
    norm_cond_sol ();
    build_TCspec true
  )


let _test_build_tree_cond_0 (v0 v1 : vprop') (vx0 vx1 : int -> vprop')
  : M.tree_cond
        (M.Tbind int int (M.Tspec int []      (fun x -> [vx0 x])     (fun _ -> True) (fun _ _ _ -> True))
               (fun x -> M.Tspec int [vx0 x] (fun y -> [v1; vx1 y]) (fun _ -> True) (fun _ _ _ -> True)))
            [v0] (fun y -> [v0; vx1 y; v1])
  = _ by (build_tree_cond true)
