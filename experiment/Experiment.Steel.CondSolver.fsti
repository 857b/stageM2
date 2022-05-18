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


#set-options "--fuel 1 --ifuel 1"

type cs_failure_goal_shape =
  | GShape_truth_refl_list
  | GShape_tree_cond

noeq
type cs_failure_enum =
  | Fail_goal_shape : (expected : cs_failure_goal_shape) -> (goal : typ) -> cs_failure_enum
  | Fail_post_unification
  | Fail_cond_sol
  | Fail_shape_unification : nat -> nat -> cs_failure_enum

noeq
type cs_failure_t = {
  fail_enum    : cs_failure_enum;
  original_exn : option exn
}

exception CSFailure of cs_failure_t

let cs_failure_to_string (f : cs_failure_t) : Tac string =
  let enum = f.fail_enum in
  let msg = term_to_string (quote enum) in
  match f.original_exn with
  | None -> msg
  | Some (TacticFailure o_msg) -> msg^"\noriginal failure: "^o_msg
  | Some o_exn -> msg^"\noriginal exception: "^term_to_string (quote o_exn)


// The following utilities are hacked to raise a failure at the location where they are called
// FIXME? raise a CSFailure exception with a meaningful location
private unfold
let cs_try (#a : Type) (f : unit -> Tac a)
           (fail_f : (cs_failure_enum -> Tac string) ->
                     TacH a (requires fun _ -> True) (ensures fun _ r -> Tactics.Result.Failed? r))
  : Tac a
  = try f ()
    with | e -> fail_f (fun ety -> let failure = {fail_enum = ety; original_exn = Some e} in
                               cs_failure_to_string failure)

private unfold
let cs_raise (#a : Type)
             (fail_f : (cs_failure_enum -> Tac string) ->
                       TacH a (requires fun _ -> True) (ensures fun _ r -> Tactics.Result.Failed? r))
  : TacH a (requires fun _ -> True) (ensures fun _ r -> Tactics.Result.Failed? r)
  = fail_f (fun ety -> let failure = {fail_enum = ety; original_exn = None} in
                    cs_failure_to_string failure)


irreducible let __cond_solver__ : unit = ()

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
    with | _ -> cs_raise (fun f -> fail (f (Fail_goal_shape GShape_truth_refl_list (cur_goal ())))))

let mk_truth_refl_list (ps : term) : Tac (list bool & term & binder) =
  let bs = fresh_uvar (Some (`(list bool))) in
  let bd, res = build (`truth_refl_list (`#ps) (`#bs)) mk_truth_refl_list_goal
  in res, bs, bd

(*let _ = assert True by (let bs,_,_ = mk_truth_refl_list (`[(1 == 1);
  (1 == 2); (2 + 2 == 4)]) in fail (term_to_string (quote bs)))*)


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


[@@ __cond_solver__]
let rec build_injection_find (#trg_n : nat) (g mask : vec trg_n bool) (i : nat)
  : Tot (option (Fin.fin (i + trg_n))) (decreases trg_n)
  = match g, mask with
  |   [],       []    -> None
  | true :: _, true :: _ -> Some i
  | _ :: g,    _ :: mask -> build_injection_find #(trg_n-1) g mask (i+1)

[@@ __cond_solver__]
let rec build_injection_iter (#src_n #trg_n : nat) (g : ograph src_n trg_n) (mask : vec trg_n bool)
  : Tot (vec src_n (option (Fin.fin trg_n))) (decreases src_n)
  = match g with
  | [] -> []
  | g0 :: g -> let y = build_injection_find g0 mask 0 in
             let mask' = match y with
                         | Some y -> Ll.set y false mask
                         | None   -> mask
             in y :: build_injection_iter #(src_n-1) g mask'

[@@ __cond_solver__]
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


[@@ __cond_solver__]
let list_of_equalities (#a : Type) (src trg : list a) : list prop =
  L.flatten (L.map (fun x -> L.map #_ #prop (fun y -> (x == y)) trg) src)

val list_of_equalities_length (#a : Type) (src trg : list a)
  : Lemma (len (list_of_equalities src trg) = len src * len trg)
          [SMTPat (L.length (list_of_equalities src trg))]

val list_of_equalities_index (#a : Type) (src trg : list a) (i : Fin.fin (len src)) (j : Fin.fin (len trg))
  : Lemma (i * len trg + j < len (list_of_equalities src trg) /\
           L.index (list_of_equalities src trg) (i * len trg + j) == (L.index src i == L.index trg j))


[@@ __cond_solver__]
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


[@@ __cond_solver__]
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


[@@ __cond_solver__]
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

[@@ __cond_solver__]
let rec filter_mask (#a : Type) (#len : nat) (mask : vec len bool) (l : vec len a)
  : Tot (vec (mask_len mask) a) (decreases l)
  = match mask, l with
  | [], [] -> []
  | true  :: mask, x :: xs -> x :: filter_mask #a #(len-1) mask xs
  | false :: mask, _ :: xs -> filter_mask #a #(len-1) mask xs

[@@ __cond_solver__]
let rec mask_push (#len : nat) (mask : vec len bool) (i : Fin.fin len {L.index mask i})
  : Tot (Fin.fin (mask_len mask))
  =
    if i = 0 then 0
    else let b :: mask = mask in
         if b then 1 + mask_push #(len-1) mask (i-1)
         else mask_push #(len-1) mask (i - 1)

[@@ __cond_solver__]
let rec mask_pull (#len : nat) (mask : vec len bool) (j : Fin.fin (mask_len mask))
  : Tot (i : Fin.fin len {L.index mask i}) (decreases mask)
  = match mask with
  | true  :: mask -> if j = 0 then 0 else 1 + mask_pull #(len - 1) mask (j - 1)
  | false :: mask -> 1 + mask_pull #(len - 1) mask j

(* TODO? optimize *)
[@@ __cond_solver__]
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

[@@ __cond_solver__]
let ij_src_mask (#src_n : nat) (#b : Type) (ij : vec src_n (option b)) : vec src_n bool
  = L.map None? ij

[@@ __cond_solver__]
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
[@@ __cond_solver__]
let rec cond_sol_unmatched (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
  : Tot (list (Fin.fin (len trg))) (decreases sl)
  = match sl with
  | CSeq  _ _ -> []
  | CSnil trg -> Ll.initi 0 (len trg) id
  | CSinj _ src trg ij sl ->
                let um = cond_sol_unmatched sl in
                let mask = ij_trg_mask ij      in
                L.map #_ #(Fin.fin (len trg)) (mask_pull mask) um

[@@ __cond_solver__]
let cond_sol_unmatched_v (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
  : list a
  = L.map (L.index trg) (cond_sol_unmatched sl)

[@@ __cond_solver__]
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

[@@ __cond_solver__]
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


[@@ __cond_solver__]
let cond_sol_to_equiv (#a : Type) (#all : bool) (#src #trg : list a) (sl : cond_sol all src trg)
  : Tot (Perm.pequiv trg L.(src @ cond_sol_unmatched_v sl))
  =
    (**) cond_sol_bij_spec sl;
    Perm.mk_perm_f (len trg) (cond_sol_bij sl)

[@@ __cond_solver__]
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
    with | _ -> cs_raise (fun f -> fail (f Fail_cond_sol))


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

(*** Building [M.prog_cond] *)

/// The front-end tactic is [build_prog_cond], which solves a goal of the form [M.prog_cond t pre post] where
/// [t], [pre] and [post] are concrete terms (i.e. do not contain uvars).
/// Internally the main work is done by [build_tree_cond] which:
/// - solves a goal of the form [M.prog_cond t pre post] where [t] and [pre] are concrete terms but
///   [post] can be an uvar
/// - returns the shape of the program as a [pre_shape_tree]


[@@ __cond_solver__]
let serialize_perm (#n : nat) (f : Perm.perm_f n) : Perm.perm_f n
  =
    let l = Perm.perm_f_to_list f in
    Perm.perm_f_of_list l

let serialize_perm_id (#n : nat) (f : Perm.perm_f n)
  : Lemma (serialize_perm f == f) [SMTPat (serialize_perm f)]
  = Perm.perm_f_extensionality (serialize_perm f) f (fun i -> ())


let normal_cond_solver : list norm_step = [
    delta_only [`%len; `%None?; `%op_Negation; `%Some?.v;
                `%L.append; `%L.flatten; `%L.hd; `%L.index; `%L.length; `%L.map; `%L.mem; `%L.op_At; `%L.splitAt;
                `%L.tail; `%L.tl;
                `%Ll.initi; `%Ll.set;
                `%Perm.mk_perm_f; `%Perm.perm_f_to_list];
    delta_attr [`%__tac_helper__; `%__cond_solver__];
    delta_qualifier ["unfold"];
    iota; zeta; primops
  ]

let norm_cond_sol () : Tac unit =
  norm normal_cond_solver

[@@ __tac_helper__]
let __defer_post_unification
      (#a : Type) (#t : M.prog_tree a) (#pre : M.pre_t) (#post0 : M.post_t a)
      (post1 : M.post_t a)
      (cd : M.tree_cond t pre post1)
      (_ : squash (post0 == post1))
  : M.tree_cond t pre post0
  = cd


/// While building the [M.tree_cond], we also want to build the associated [M.shape_tree].
/// This is done by extracting a [pre_shape_tree]. At the end, [build_prog_cond] quotes the [pre_shape_tree],
/// converts it to a [M.shape_tree] (by using an effective test, [shape_tree_of_pre]) and check that it matches
/// the built [M.tree_cond] (again with an effective test, [M.tree_cond_has_shape]).

let tc_extract_nat () : Tac nat =
  norm_cond_sol ();
  extract_nat_tac ()

[@@ __tac_helper__]
private
let __extract_perm (#n : nat) (f : Perm.perm_f n) : Type
  = extract_term #(list int) (Ll.initi 0 n f)

let tc_extract_perm (n : nat) : Tac (list int) =
  norm_cond_sol ();
  extract_term_tac (unquote #(list int))

type pre_shape_tree : (pre_n : int) -> (post_n : int) -> Type =
  | PSspec  : (pre_n : int) -> (post_n : int) -> (frame_n : int) ->
              (p0 : list int) -> (p1 : list int) ->
              pre_shape_tree (pre_n + frame_n) (post_n + frame_n)
  | PSret   : (n : int) -> (p : list int) ->
              pre_shape_tree n n
  | PSbind  : (pre_n : int) -> (itm_n : int) -> (post_n : int) ->
              (f : pre_shape_tree pre_n itm_n) -> (g : pre_shape_tree itm_n post_n) ->
              pre_shape_tree pre_n post_n
  | PSbindP : (pre_n : int) -> (post_n : int) ->
              (g : pre_shape_tree pre_n post_n) ->
              pre_shape_tree pre_n post_n

type shape_tree_t = (pre_n : nat & post_n : nat & pre_shape_tree pre_n post_n)

let rec shape_tree_of_pre (#pre_n : nat) (#post_n : nat) (ps : pre_shape_tree pre_n post_n)
  : Tot (option (M.shape_tree pre_n post_n)) (decreases ps)
  = match ps with
  | PSspec pre_n post_n frame_n p0 p1 ->
           if pre_n >= 0 && post_n >= 0 && frame_n >= 0
           then match Perm.perm_f_list_checked p0, Perm.perm_f_list_checked p1 with
           | Some p0, Some p1 -> Some (M.Sspec pre_n post_n frame_n p0 p1)
           | _ -> None
           else None
  | PSret n p ->
          (match Perm.perm_f_list_checked p with
          | Some p -> Some (M.Sret n p)
          | _ -> None)
  | PSbind pre_n itm_n post_n f g ->
          if itm_n >= 0
          then match shape_tree_of_pre f, shape_tree_of_pre g with
          | Some f, Some g -> Some (M.Sbind pre_n itm_n post_n f g)
          | _ -> None
          else None
  | PSbindP pre_n post_n g ->
          (match shape_tree_of_pre g with
          | Some g -> Some (M.SbindP pre_n post_n g)
          | _ -> None)


/// The following tactics solve goals of the form [M.tree_cond t pre t_post] where [t_post] is a concrete term if
/// the boolean parameter [post] is set and an uvar otherwise.
/// The resolution is done by solving some [cond_sol] problems. By branching on the [post] parameter, one can
/// ensure that those problems are fully instantiated. That is we use different building functions depending on
/// whether the post-condition is known ('_p' (post) functions like [__build_TCspec_p]) or has to be
/// inferred ('_u' (uvar) functions like [__build_TCspec_u]).

[@@ __tac_helper__]
let __build_TCspec_u
      (#a : Type) (#pre : M.pre_t) (#post : M.post_t a) (#req : M.req_t pre) (#ens : M.ens_t pre a post)
      (#pre' : M.pre_t)
      (cs0 : cond_sol false pre pre')

      (pre_n   : extract_term (L.length pre))
      (post_n  : (x : a) -> extract_term (L.length (post x)))
      (frame_n : extract_term (L.length (cond_sol_unmatched cs0)))
      (p0 : __extract_perm (cond_sol_to_equiv cs0))

  : M.tree_cond (M.Tspec a pre post req ens) pre' (fun (x : a) -> L.(post x @ cond_sol_unmatched_v cs0))
  =
    let frame = cond_sol_unmatched_v cs0 in
    M.TCspec pre' (fun x -> L.(post x @ frame)) frame
             (serialize_perm (cond_sol_to_equiv cs0))
             (fun x -> Perm.id_n (len L.(post x @ frame)))

[@@ __tac_helper__]
let __build_TCspec_p
      (#a : Type) (#pre : M.pre_t) (#post : M.post_t a) (#req : M.req_t pre) (#ens : M.ens_t pre a post)
      (#pre' : M.pre_t) (#post' : M.post_t a)
      (cs0 : cond_sol false pre pre')
      (cs1 : (x : a) -> cond_sol true (post' x) L.(post x @ cond_sol_unmatched_v cs0))

      (pre_n   : extract_term (L.length pre))
      (post_n  : (x : a) -> extract_term (L.length (post x)))
      (frame_n : extract_term (L.length (cond_sol_unmatched cs0)))
      (p0 : __extract_perm (cond_sol_to_equiv cs0))
      (p1 : (x : a) -> __extract_perm (cond_sol_all_to_equiv (cs1 x)))

  : M.tree_cond (M.Tspec a pre post req ens) pre' post'
  =
    M.TCspec pre' post' (cond_sol_unmatched_v cs0)
             (serialize_perm (cond_sol_to_equiv cs0))
             (fun x -> serialize_perm (cond_sol_all_to_equiv (cs1 x)))


/// By default, if the post-condition of a [M.Tret] has to be inferred, we simply choose [fun _ -> pre]. That is,
/// we do not introduce any dependency in the returned value.
/// It is possible to modify this behaviour by annotating the [M.Tret] with [sl_hint : M.post_t a], which
/// specifies some vprops that should depend on the returned value (it does not need to mention the vprops that
/// do not depend on the returned value).
/// The default behaviour is obtained with [sl_hint = fun _ -> []].
/// This hint is ignored if the post-condition is known from the context ([__build_TCret_p]).
/// See [test_build_tree_cond__Tret_u_0] for a minimal example where it is needed.
[@@ __tac_helper__]
let __build_TCret_u
      (#a : Type) (#x : a) (#sl_hint : M.post_t a)
      (#pre : M.pre_t)
      (cs : cond_sol false (sl_hint x) pre)
      
      (n : extract_term (L.length pre))
      (p : __extract_perm (cond_sol_to_equiv cs))

  : M.tree_cond (M.Tret a x sl_hint) pre (fun x -> L.(sl_hint x @ cond_sol_unmatched_v cs))
  =
    M.TCret pre (fun x -> L.(sl_hint x @ cond_sol_unmatched_v cs))
            (serialize_perm (cond_sol_to_equiv cs))

[@@ __tac_helper__]
let __build_TCret_p
      (#a : Type) (#x : a) (#sl_hint : M.post_t a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (cs : cond_sol true (post x) pre)

      (n : extract_term (L.length pre))
      (p : __extract_perm (cond_sol_all_to_equiv cs))

  : M.tree_cond (M.Tret a x sl_hint) pre post
  =
    M.TCret #a #x pre post (serialize_perm (cond_sol_all_to_equiv cs))


let build_TCspec (post : bool) : Tac shape_tree_t
  = if post then begin
      apply_raw (`__build_TCspec_p);
      build_cond_sol false;
      norm_cond_sol ();
      let x = intro () in
      build_cond_sol true
    end else begin
      // FIXME : why apply_raw shelves cs0 ?
      let cs0 = fresh_uvar None in
      apply_raw (`(__build_TCspec_u (`#cs0)));
      unshelve cs0;
      build_cond_sol false
    end;

    let pre_n   = tc_extract_nat () in
    let post_n  = let _ = intro () in tc_extract_nat () in
    let frame_n = tc_extract_nat () in
    let p0 = tc_extract_perm (pre_n + frame_n)
    in let p1 : list int =
      if post then let _ = intro () in tc_extract_perm (post_n + frame_n)
      else Ll.initi 0 (post_n + frame_n) id
    in
    (|pre_n + frame_n, post_n + frame_n, PSspec pre_n post_n frame_n p0 p1|)

let build_TCret (post : bool) : Tac shape_tree_t
  = if post then begin
      apply_raw (`__build_TCret_p);
      build_cond_sol true
    end else begin
      let cs = fresh_uvar None in
      apply_raw (`(__build_TCret_u (`#cs)));
      unshelve cs;
      build_cond_sol false
    end;

    let n = tc_extract_nat () in
    let p = tc_extract_perm n in
    (|n, n, PSret n p|)

let rec build_TCbind (post : bool) : Tac shape_tree_t
  = apply (`M.TCbind);
    let (|pre_f, post_f, s_f|) = build_tree_cond false in
    let x = intro () in
    let (|pre_g, post_g, s_g|) = build_tree_cond post  in

    if post_f <> pre_g then cs_raise (fun f -> fail (f (Fail_shape_unification post_f pre_g)));
    (|pre_f, post_g, PSbind pre_f post_f post_g s_f s_g|)

and build_TCbindP (post : bool) : Tac shape_tree_t
  = apply (`M.TCbindP);
    let x = intro () in
    let (|pre_g, post_g, s_g|) = build_tree_cond post in
    (|pre_g, post_g, PSbindP pre_g post_g s_g|)

and build_tree_cond (post : bool) : Tac shape_tree_t
  =
    let build_tac : bool -> Tac shape_tree_t =
      let goal = cur_goal () in
      let args = (collect_app goal)._2 in
      if L.length args <> 4
      then cs_raise (fun f -> fail (f (Fail_goal_shape GShape_tree_cond goal)))
      else let hd = (collect_app (L.index args 1)._1)._1 in
      match inspect hd with
      | Tv_FVar fv ->
          // TODO? better solution to match
          let nd = inspect_fv fv in
          if Nil? nd then cs_raise (fun f -> fail (f (Fail_goal_shape GShape_tree_cond goal)));
          begin match L.last nd with
          | "Tspec"  -> build_TCspec
          | "Tret"   -> build_TCret 
          | "Tbind"  -> build_TCbind
          | "TbindP" -> build_TCbindP
          | _ -> cs_raise (fun f -> fail (f (Fail_goal_shape GShape_tree_cond goal)))
          end
      | _ -> cs_raise (fun f -> fail (f (Fail_goal_shape GShape_tree_cond goal)))
    in
    if post
    then build_tac true
    else begin
      // If post is false, the post is an uvar [post0] that may be independent of some bound variables the current
      // [M.prog_tree] and pre can depend on.
      // If we try to build directly a [tree_cond_sol] for [post0], the unification can fail since we need
      // to normalize the inferred post in order to see the variables it depends on.
      // Hence we introduce a fresh uvar [post1] for the inferred post. [post1] can depend on all the variables
      // in scope but should (in a correct program) only depends on the variables in scope for [post0].
      // We then normalize [post1] and try to assign the result to [post0].
      let post1 = fresh_uvar None in
      // Changes the goal [tree_cond_sol t pre ?post0] into [tree_cond_sol t pre ?post1] and [?post0 == ?post1]
      apply_raw (`(__defer_post_unification (`#post1)));
      // Solves [tree_cond_sol t pre post1]
      let shp = build_tac false in
      // [?post1] is now inferred as [post1] and we are presented with a goal [?post0 == post1].
      // We normalize [post1] and assign the result to [?post0].
      norm_cond_sol ();
      cs_try trefl (fun f -> fail (f Fail_post_unification));

      shp
    end


[@@ __tac_helper__]
private inline_for_extraction
let __build_prog_cond
      (#a : Type) (#t : M.prog_tree a) (#pre : M.pre_t) (#post : M.post_t a)
      (tc0 : M.tree_cond t pre post)
      (#tc : M.tree_cond t pre post) (_ : squash (tc == tc0)) // allows to normalize tc
      (#pre_n : int) (#post_n : int) (ps : pre_shape_tree pre_n post_n)
      (_ : squash (pre_n >= 0 /\ post_n >= 0 /\ pre_n == len pre))
      (#s : M.shape_tree pre_n post_n) (_ : squash (Some s == shape_tree_of_pre ps))
      (_ : M.tree_cond_has_shape tc s)
  : M.prog_cond t pre post
  = M.({ pc_tree     = tc;
         pc_post_len = post_n;
         pc_shape    = s })

let intro_l_True : l_True = ()
let intro_squash_l_True : squash (l_True) = ()

/// This is the front-end tactics. It solves a goal of the form [M.prog_cond t pre post].
let build_prog_cond () : Tac unit
  = 
    let tc0   = fresh_uvar None in
    let tc_eq = fresh_uvar None in
    let ushp  = fresh_uvar None in
    apply (`(__build_prog_cond (`#tc0) (`#tc_eq) (`#ushp)));
    // [M.tree_cond t pre post]
    unshelve tc0;
    let (|pre_n, post_n, shp|) = build_tree_cond true in
    // tc <- tc0
    unshelve tc_eq;
    norm_cond_sol ();
    trefl ();
    // shp
    unshelve ushp;
    exact (quote shp);
    // some checks
    norm [delta_only [`%L.length; `%len]; iota; zeta; primops; simplify];
    exact (`intro_squash_l_True);
    // [shape_tree_of_pre]
    norm [delta_only [`%shape_tree_of_pre;
                      `%Perm.perm_f_list_checked; `%Perm.check_list_injective;
                      `%L.length; `%L.hd; `%L.tl; `%L.tail; `%Ll.initi; `%L.index; `%L.list_ref; `%Ll.set
                     ];
          iota; zeta; primops];
    trefl ();
    // [M.tree_cond_has_shape tc shp]
    norm [delta_only [`%M.tree_cond_has_shape; `%Perm.perm_f_to_list; `%Perm.mk_perm_f; `%Perm.mk_perm_f;
                      `%Perm.perm_f_eq; `%Perm.perm_f_of_list; `%Perm.id_n;
                      `%L.length; `%L.hd; `%L.tl; `%L.tail; `%L.index; `%Ll.initi; `%Ll.list_eq;
                      `%U.cast];
          delta_qualifier ["unfold"];
          iota; zeta; primops; simplify];
    exact (`intro_l_True)
