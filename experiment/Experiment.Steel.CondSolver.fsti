module Experiment.Steel.CondSolver

module M    = Experiment.Steel.Repr.M
module U    = Learn.Util
module L    = FStar.List.Pure
module Ll   = Learn.List
module SE   = Steel.Effect
module Msk  = Learn.List.Mask
module Fin  = FStar.Fin
module Opt  = Learn.Option
module Perm = Learn.Permutation

open FStar.Tactics
open Learn.Tactics.Util
open FStar.Mul
open Experiment.Steel.Interface


#set-options "--fuel 1 --ifuel 1"

irreducible let __cond_solver__ : unit = ()


type cs_context = unit -> list info

let dummy_ctx = fun () -> []

let ctx_app_loc (c : cs_context) (m : string) : cs_context
  = fun () -> Info_location m :: c ()

// The following utilities are hacked to raise a failure at the location where they are called
// FIXME? raise a Failure exception with a meaningful location
private unfold
let cs_try (#a : Type) (f : unit -> Tac a)
           (fr : flags_record) (ctx : cs_context)
           (fail_f : (failure_enum -> list info -> Tac string) ->
                     TacH a (requires fun _ -> True) (ensures fun _ r -> Tactics.Result.Failed? r))
  : Tac a
  = try f ()
    with | e -> fail_f (fun fail_enum infos ->
                 let failure = {fail_enum; fail_info = L.(infos @ ctx () @ [Info_original_exn e])} in
                 failure_to_string fr failure)

private unfold
let cs_raise (#a : Type)
             (fr : flags_record) (ctx : cs_context)
             (fail_f : (failure_enum -> list info -> Tac string) ->
                       TacH a (requires fun _ -> True) (ensures fun _ r -> Tactics.Result.Failed? r))
  : TacH a (requires fun _ -> True) (ensures fun _ r -> Tactics.Result.Failed? r)
  = fail_f (fun fail_enum infos -> let
      failure = {fail_enum; fail_info = L.(infos @ ctx ())} in
      failure_to_string fr failure)


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

let build_truth_refl_list fr ctx : Tac (list bool) =
  norm [iota; primops; simplify];
  repeatb (fun () ->
    try (apply (`ReflLNil); None)
    with | _ -> try (apply (`ReflLTrue); Some true)
    with | _ -> try (apply (`ReflLFalse); Some false)
    with | _ -> cs_raise fr ctx (fun m -> fail (m (Fail_goal_shape GShape_truth_refl_list)
                                              [Info_goal (cur_goal ())])))

let mk_truth_refl_list fr ctx (ps : term) : Tac (list bool & term & binder) =
  let bs = fresh_uvar (Some (`(list bool))) in
  let bd, res = build (`truth_refl_list (`#ps) (`#bs)) (fun () -> build_truth_refl_list fr ctx)
  in res, bs, bd

(*let _ = assert True by (let bs,_,_ = mk_truth_refl_list (`[(1 == 1);
  (1 == 2); (2 + 2 == 4)]) in fail (term_to_string (quote bs)))*)


(*** Building a [M.vprop_with_emp] *)

#push-options "--ifuel 2"
(**) private val __begin_opt_0 : unit

/// Solves a goal [vprop_with_emp vp]
let rec build_vprop_with_emp fr ctx : Tac unit =
  try apply (`M.VeUnit) with | _ -> 
  match catch (fun () -> apply (`M.VeStar)) with
  | Inr () -> build_vprop_with_emp fr ctx; (* left  *)
             build_vprop_with_emp fr ctx  (* right *)
  | Inl _ ->
  try apply (`M.VeEmp ) with | _ ->
    cs_raise fr ctx (fun m -> fail (m (Fail_goal_shape GShape_vprop) [Info_goal (cur_goal ())]))

#pop-options
(**) private val __end_opt_0 : unit


(*** Finding an element in a list *)

let elem_index (#a : Type) (x : a) (l : list a) =
  i : Fin.fin (L.length l) { L.index l i == x }

[@@ __cond_solver__]
let rec findi_true (l : list bool)
  : option (i : Fin.fin (L.length l) {L.index l i})
  = match l with
  | [] -> None
  | true :: _ -> Some 0
  | false :: tl -> Opt.map (fun (i : Fin.fin (L.length tl) {L.index tl i}) ->
                             1 + i <: (i : Fin.fin (L.length l) {L.index l i}))
                         (findi_true tl)

[@@ __tac_helper__]
let __build_elem_index
      #a (#x : a) (#l : list a) (#bs : list bool)
      (rfl : truth_refl_list (L.map #a #prop (fun y -> (x == y)) l) bs)
      #i (i_eq : squash (Some i == findi_true bs))
  : elem_index x l
  = (**) truth_refl_list_index rfl i;
    i

/// Solves a goal of the form [elem_index x l]
let build_elem_index fr ctx : Tac unit =
  let goal = cur_goal () in
  apply (`__build_elem_index);
  norm [delta_only [`%L.map]; iota; zeta];
  let _ = build_truth_refl_list fr ctx in
  norm [delta_only [`%findi_true; `%Opt.map];
       iota; zeta; primops];
  cs_try trefl fr ctx (fun m -> fail (m Fail_elem_index [Info_goal goal]))


(*** Building a [M.to_repr_t] *)

/// Steps for normalizing [M.flatten_vprop v].
let __normal_flatten_vprop : list norm_step = [
  delta_only [`%M.flatten_vprop; `%M.flatten_vprop_aux];
  delta_attr [`%SE.__reduce__];
  delta_qualifier ["unfold"];
  iota; zeta; primops
]

/// Steps for the normalisation of Steel's requires and ensures clauses.
/// We use:
/// - [__steel_reduce__] to unfold the selector functions (for instance [Steel.Reference.sel]).
/// - [__inner_steel_reduce__] to unfold [focus_rmem]
let __normal_Steel_logical_spec : list norm_step = [
  delta_only [`%SE.VUnit?._0];
  delta_attr [`%SE.__reduce__; `%SE.__steel_reduce__; `%SE.__inner_steel_reduce__];
  delta_qualifier ["unfold"];
  iota; zeta; primops
]


val __build_to_repr_t_lem
      (p : SE.vprop) (r_p : M.vprop_list {p `SE.equiv` M.vprop_of_list r_p}) (h : SE.rmem p)
      (v : SE.vprop{SE.can_be_split p v}) (_ : squash (SE.VUnit? v))
      (i : elem_index (SE.VUnit?._0 v) r_p)
      (i' : int) (_ : squash (i' == i))
  : squash (h v ==
        M.sel r_p (SE.equiv_can_be_split p (M.vprop_of_list r_p);
                   SE.focus_rmem h (M.vprop_of_list r_p)) i)

[@@ __tac_helper__]
let __build_to_repr_t
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)

      (e_pre  : M.vprop_with_emp pre) (r_pre  : M.pre_t)
      (pre_eq  : squash (r_pre == M.flatten_vprop e_pre))

      (e_post : (x : a) -> M.vprop_with_emp (post x)) (r_post : M.post_t a)
      (post_eq : (x : a) -> squash (r_post x == M.flatten_vprop (e_post x)))

      (#r_req  : M.req_t r_pre)
      (r_req_eq  : (h0 : SE.rmem pre) -> (sl0 : M.sl_f r_pre) ->
                   (sl0_eq : ((v : SE.vprop{SE.can_be_split pre v}) -> squash (SE.VUnit? v) ->
                             (i : elem_index (SE.VUnit?._0 v) r_pre) ->
                             // This indirection is needed so that [apply_raw] presents a goal for [i]
                             (i' : int) -> (_ : squash (i' == i)) ->
                             squash (h0 v == sl0 i'))) ->
                    r_req sl0 == req h0)

      (#r_ens  : M.ens_t r_pre a r_post)
      (r_ens_eq  : (h0 : SE.rmem pre) -> (sl0 : M.sl_f r_pre) ->
                   (x : a) ->
                   (h1 : SE.rmem (post x)) -> (sl1 : M.sl_f (r_post x)) ->
                   (sl0_eq : ((v : SE.vprop{SE.can_be_split pre v}) -> squash (SE.VUnit? v) ->
                             (i : elem_index (SE.VUnit?._0 v) r_pre) ->
                             (i' : int) -> (_ : squash (i' == i)) ->
                             squash (h0 v == sl0 i'))) ->
                   (sl1_eq : ((v : SE.vprop{SE.can_be_split (post x) v}) -> squash (SE.VUnit? v) ->
                             (i : elem_index (SE.VUnit?._0 v) (r_post x)) ->
                             (i' : int) -> (_ : squash (i' == i)) ->
                             squash (h1 v == sl1 i'))) ->
                   r_ens sl0 x sl1 == ens h0 x h1)

  : M.to_repr_t a pre post req ens
  = 
    let r_pre_eq () : Lemma (pre `SE.equiv` M.vprop_of_list r_pre)
      = pre_eq;
        M.vprop_equiv_flat pre e_pre;
        SE.equiv_sym (M.vprop_of_list r_pre) pre                in
    let r_post_eq (x : a) : Lemma (post x `SE.equiv` M.vprop_of_list (r_post x))
      = post_eq x;
        M.vprop_equiv_flat (post x) (e_post x);
        SE.equiv_sym (M.vprop_of_list (r_post x)) (post x)
    in
    {
    r_pre; r_post; r_req; r_ens;
    r_pre_eq; r_post_eq;
    r_req_eq  = (fun (h0 : SE.rmem pre) ->
                   r_pre_eq ();
                   SE.equiv_can_be_split pre (M.vprop_of_list r_pre);
                   let h0_r = SE.focus_rmem h0 (M.vprop_of_list r_pre) in
                   r_req_eq h0 (M.sel r_pre h0_r)
                            (__build_to_repr_t_lem pre r_pre h0));
    r_ens_eq  = (fun (h0 : SE.rmem pre) (x : a) (h1 : SE.rmem (post x)) ->
                   r_pre_eq ();
                   SE.equiv_can_be_split pre (M.vprop_of_list r_pre);
                   let h0_r = SE.focus_rmem h0 (M.vprop_of_list r_pre) in
                   r_post_eq x;
                   SE.equiv_can_be_split (post x) (M.vprop_of_list (r_post x));
                   let h1_r = SE.focus_rmem h1 (M.vprop_of_list (r_post x)) in
                   r_ens_eq h0 (M.sel r_pre h0_r) x h1 (M.sel (r_post x) h1_r)
                            (__build_to_repr_t_lem pre r_pre h0)
                            (__build_to_repr_t_lem (post x) (r_post x) h1))
  }

let filter_rmem_apply (#p : SE.vprop) (h : SE.rmem p) (v : SE.vprop{SE.can_be_split p v})
  #sl (_ : squash (h v == sl))
  : squash (h v == sl)
  = ()

/// Given a term [squash (lhs == rhs)], this tactics returns [Some (h, v)] if [lhs] is [h v]
/// UNUSED: using v generates a SMT goal [SE.can_be_split]
let match_rmem_apply (t : term) : Tac (option (term & term))
  = match inspect t with
    | Tv_App _squash (eq, Q_Explicit) ->
      let _, ts = collect_app eq in
      let n_args = L.length ts in
      if n_args <> 3 then fail ("unexpected shape1:"^string_of_int n_args)
      else let lhs = (L.index ts 1)._1 in
     (match inspect lhs with
      | Tv_App h (v, Q_Explicit) -> Some (h, v)
      | _ -> None)
    | _ -> fail "unexpected shape0"

#push-options "--ifuel 2"
(**) private val __begin_opt_1 : unit

/// Solves a goal [to_repr_t a pre post req ens]
let build_to_repr_t fr ctx : Tac unit
  =
    let u_r_pre  = fresh_uvar None in
    let u_r_post = fresh_uvar None in
    let u_r_req  = fresh_uvar None in
    let u_r_ens  = fresh_uvar None in
    apply_raw (`__build_to_repr_t);

    (* [r_pre] *)
    let ctx_pre = ctx_app_loc ctx "in the pre-condition" in
    build_vprop_with_emp fr ctx_pre;
    exact u_r_pre;
    norm __normal_flatten_vprop;
    trefl ();

    (* [r_post] *)
    let ctx_post = ctx_app_loc ctx "in the post-condition" in
    let _ = intro () in
      build_vprop_with_emp fr ctx_post;
    exact u_r_post;
    let _ = intro () in
      norm __normal_flatten_vprop;
      trefl ();

    // apply the rewriting hypothesis [eq_lem] to solve a goal [squash (h v == sl ?i)]
    let apply_rew ctx eq_lem =
      let u_i' = fresh_uvar None in
      apply_raw eq_lem;
      // [VUnit?]
      norm [delta_only [`%SE.VUnit?]; iota];
      trivial ();
      // [elem_index]
      norm __normal_Steel_logical_spec;
      build_elem_index fr ctx;
      // [i']
      exact u_i';
      // [i' <- i]
      norm [delta_attr [`%__cond_solver__; `%__tac_helper__]];
      trefl ()
    in

    (* [r_req] *)
    let ctx_req = ctx_app_loc ctx "in the requires" in
    exact u_r_req;
    let h0 = intro () in let sl0 = intro () in let eq0 = intro () in
      // This normalisation has to be done after introducing [eq0], otherwise its application fails,
      // seemingly because of the normalisation of [t_of].
      norm __normal_Steel_logical_spec;
      pointwise' begin fun () ->
        match catch (fun () -> apply_raw (`filter_rmem_apply (`#(binder_to_term h0)))) with
        | Inr () -> // For some reason, this can only be applied on the goal produced by [filter_rmem_apply]
                   // TODO? we could check that [filter_rmem_apply] has not succeeded by instantiating an uvar
                   apply_rew ctx_req eq0
        | Inl _  -> trefl ()
      end;
      cs_try trefl fr ctx_req (fun m -> fail (m Fail_elem_index []));

    (* [r_ens] *)
    let ctx_ens = ctx_app_loc ctx "in the ensures" in
    exact u_r_ens;
    let h0  = intro () in let sl0 = intro () in
    let x   = intro () in
    let h1  = intro () in let sl1 = intro () in
    let eq0 = intro () in let eq1 = intro () in
      norm __normal_Steel_logical_spec;
      pointwise' begin fun () ->
        match catch (fun () -> apply_raw (`filter_rmem_apply (`#(binder_to_term h0)))) with
        | Inr () -> apply_rew ctx_ens eq0
        | Inl _ ->
        match catch (fun () -> apply_raw (`filter_rmem_apply (`#(binder_to_term h1)))) with
        | Inr () -> apply_rew ctx_ens eq1
        | Inl _  -> trefl ()
      end;
      cs_try trefl fr ctx_ens (fun m -> fail (m Fail_elem_index []))

#pop-options
(**) private val __end_opt_1 : unit


(*** Building an injection *)

let len (#a : Type) : list a -> nat = L.length #a

/// Graph over-approximation
type ograph (src_n : nat) (trg_n : nat) = Ll.vec src_n (Ll.vec trg_n bool)

let injective_on_dom (#a #b : Type) (f : a -> option b) : prop =
  forall (x x' : a) . Some? (f x) /\ f x == f x' ==> x == x'

let injective_on_domI (#a #b : Type) (f : a -> option b)
                      (prf : (x : a) -> (x' : a) -> Lemma (requires Some? (f x) /\ f x == f x') (ensures x == x'))
  : Lemma (injective_on_dom f)
  = FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 prf)


[@@ __cond_solver__]
let rec build_injection_find (#trg_n : nat) (g mask : Ll.vec trg_n bool) (i : nat)
  : Tot (option (Fin.fin (i + trg_n))) (decreases trg_n)
  = match g, mask with
  |   [],       []    -> None
  | true :: _, true :: _ -> Some i
  | _ :: g,    _ :: mask -> build_injection_find #(trg_n-1) g mask (i+1)

[@@ __cond_solver__]
let rec build_injection_iter (#src_n #trg_n : nat) (g : ograph src_n trg_n) (mask : Ll.vec trg_n bool)
  : Tot (Ll.vec src_n (option (Fin.fin trg_n))) (decreases src_n)
  = match g with
  | [] -> []
  | g0 :: g -> let y = build_injection_find g0 mask 0 in
             let mask' = match y with
                         | Some y -> Ll.set y false mask
                         | None   -> mask
             in y :: build_injection_iter #(src_n-1) g mask'

[@@ __cond_solver__]
let build_injection (#src_n #trg_n : nat) (g : ograph src_n trg_n)
  : Tot (Ll.vec src_n (option (Fin.fin trg_n)))
  = build_injection_iter g (Ll.initi 0 trg_n (fun _ -> true))


val build_injection_find_spec (#trg_n : nat) (g mask : Ll.vec trg_n bool) (i : nat)
  : Lemma (requires Some? (build_injection_find g mask i))
          (ensures (let j = Some?.v (build_injection_find g mask i) - i in
                    j >= 0 /\ L.index g j /\ L.index mask j))

val build_injection_iter_spec (#src_n #trg_n : nat) (g : ograph src_n trg_n) (mask : Ll.vec trg_n bool)
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
  f : Ll.vec (len src) (option (Fin.fin (len trg))) {
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
let rec list_to_matrix (#a : Type) (n0 n1 : nat) (l : Ll.vec (n0 * n1) a)
  : Tot (Ll.vec n0 (Ll.vec n1 a)) (decreases n0)
  = if n0 = 0 then []
    else let l0, ls = L.splitAt n1 l in
         (**) L.splitAt_length n1 l;
         l0 :: list_to_matrix(n0 - 1) n1 ls

val list_to_matrix_index (#a : Type) (n0 n1 : nat) (l : Ll.vec (n0 * n1) a) (i : Fin.fin n0) (j : Fin.fin n1)
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
let __build_partial_injection (#a : Type) (src trg : list a) (bs : list bool)
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
  delta_only [`%__build_partial_injection; `%ograph_of_equalities; `%list_to_matrix; `%L.splitAt;
              `%L.length; `%Ll.initi; `%len; `%Ll.set;
              `%build_injection; `%build_injection_iter; `%build_injection_find];
  iota; zeta; primops]

/// solves a goal of the form [partial_injection src dst]
let build_partial_injection fr ctx : Tac unit =
  apply (`__build_partial_injection);
  norm normal_list_of_equalities;
  let _ : list _ = build_truth_refl_list fr ctx in
  ()


(*let test_inj : partial_injection ['a';'b';'c';'a';'b'] ['a';'c';'b';'d';'e';'a'] =
  _ by (build_partial_injection ())

let _ = assert (U.print_util test_inj)
            by (norm [delta_only [`%test_inj]];
                norm normal_build_partial_injection;
                fail "print")*)

(*let _ : partial_injection ['a';'b';'c';'a';'b'] ['a';'c';'b';'d';'e';'a'] =
  _ by (let goal = cur_goal () in
        let inj, () = build_term goal build_partial_injection in
        exact inj)*)


(*** Building a [M.vequiv] *)

/// [vequiv_sol all src trg] represents the building of a [M.vequiv trg src].
/// The order of the arguments is reversed since we build an injection ([M.veq_eq]) from [src] to [trg].
/// If [all] is not set, we allow some elements of [trg] to be left unmatched. In that case [src] needs to be
/// completed with [src_add] in order to obtain a [M.vequiv].
// TODO? represent veq.veq_eq with a list
[@@ __cond_solver__]
noeq
type vequiv_sol : (all : bool) -> (src : M.vprop_list) -> (trg : M.vprop_list) -> Type =
  | VeqAll : (src : M.vprop_list) -> (trg : M.vprop_list) ->
             (veq : M.vequiv trg src) ->
             vequiv_sol true src trg
  | VeqPrt : (src : M.vprop_list) -> (unmatched : M.vprop_list) -> (trg : M.vprop_list) ->
             (veq : M.vequiv trg L.(src@unmatched)) ->
             vequiv_sol false src trg

[@@ __cond_solver__]
let vequiv_sol_all (#src #trg : M.vprop_list) (e : vequiv_sol true src trg)
  : M.vequiv trg src
  = VeqAll?.veq e

[@@ __cond_solver__]
let vequiv_sol_prt (#src #trg : M.vprop_list) (e : vequiv_sol false src trg)
  : M.vequiv trg L.(src @ VeqPrt?.unmatched e)
  = VeqPrt?.veq e


[@@ __cond_solver__]
let vequiv_sol_end (all : bool) (vs : M.vprop_list) : vequiv_sol all vs vs
  = if all then VeqAll vs vs (M.vequiv_refl vs) else VeqPrt vs [] vs (M.vequiv_refl vs)

[@@ __cond_solver__]
let vequiv_sol_end_prt (trg : M.vprop_list) : vequiv_sol false [] trg
  = VeqPrt [] trg trg (M.vequiv_refl trg)


(**** [vequiv_sol_inj] *)

/// Masks to select the elements that have *not* been matched

[@@ __cond_solver__]
let ij_src_mask (#src_n : nat) (#b : Type) (ij : Ll.vec src_n (option b)) : Ll.vec src_n bool
  = L.map None? ij

[@@ __cond_solver__]
let ij_trg_mask (#src_n #trg_n : nat) (ij : Ll.vec src_n (option (Fin.fin trg_n))) : Ll.vec trg_n bool
  = Ll.initi 0 trg_n (fun j -> not (L.mem (Some j) ij))

/// Number of matched elements i.e. number of [Some]
let ij_matched_n (#a : Type) (#src #trg : list a) (ij : partial_injection src trg) : nat
  = Msk.mask_len (Msk.mask_not (ij_src_mask ij))

let ij_matched_perm_f (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
                    (i : Fin.fin (Msk.mask_len (Msk.mask_not (ij_src_mask ij))))
  : Fin.fin (Msk.mask_len (Msk.mask_not (ij_trg_mask ij)))
  =
    let i0 = Msk.mask_pull (Msk.mask_not (ij_src_mask ij)) i in
    let j0 = Some?.v (L.index ij i0) in
    (**) L.lemma_index_memP ij i0;
    Msk.mask_push (Msk.mask_not (ij_trg_mask ij)) j0

val ij_matched_perm_f_injective
      (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (Perm.injective (ij_matched_perm_f ij))

val ij_matched_perm_f_surjective
      (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (Perm.surjective (ij_matched_perm_f ij))

val ij_matched_len (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (Msk.mask_len (Msk.mask_not (ij_trg_mask ij)) = Msk.mask_len (Msk.mask_not (ij_src_mask ij)))

let ij_matched_perm (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Perm.perm_f (ij_matched_n ij)
  = 
    (**) ij_matched_perm_f_injective ij;
    (**) ij_matched_len ij;
    Perm.mk_perm_f _ (ij_matched_perm_f ij)

val ij_matched_perm_eq (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (ij_matched_len ij;
           Msk.filter_mask (Msk.mask_not (ij_src_mask ij)) src ==
           Perm.apply_perm_r (ij_matched_perm ij) (Msk.filter_mask (Msk.mask_not (ij_trg_mask ij)) trg))

let ij_matched_equiv (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Perm.pequiv (Msk.filter_mask (Msk.mask_not (ij_trg_mask ij)) trg)
                (Msk.filter_mask (Msk.mask_not (ij_src_mask ij)) src)
  =
    (**) let l_trg = Msk.filter_mask (Msk.mask_not (ij_trg_mask ij)) trg in
    (**) ij_matched_len ij;
    (**) ij_matched_perm_eq ij;
    U.cast (Perm.perm_f (L.length l_trg)) (ij_matched_perm ij)


[@@ __cond_solver__]
let vequiv_inj_eq
      (#src #trg : M.vprop_list)
      (ij : partial_injection src trg)
      (e' : M.vequiv (Msk.filter_mask (ij_trg_mask ij) trg) (Msk.filter_mask (ij_src_mask ij) src))
  : M.veq_eq_t (len trg) (len src)
  =
    let mask_src = ij_src_mask ij in
    let mask_trg = ij_trg_mask ij in
    M.mk_veq_eq (len trg) (len src) (L.index
        (Msk.merge_fun_on_mask mask_src #(option (Fin.fin (len trg)))
        (fun _ j -> Opt.map (Msk.mask_pull mask_trg) (e'.veq_eq j))
        (fun i   -> L.index ij i)))

val vequiv_inj_typ
      (#src #trg : M.vprop_list)
      (ij : partial_injection src trg)
      (e' : M.vequiv (Msk.filter_mask (ij_trg_mask ij) trg) (Msk.filter_mask (ij_src_mask ij) src))
  : squash (M.veq_typ_eq (M.vprop_list_sels_t trg) (M.vprop_list_sels_t src)
                         (U.cast _ (vequiv_inj_eq ij e')))

val vequiv_inj_g
      (#src #trg : M.vprop_list)
      (ij : partial_injection src trg)
      (e' : M.vequiv (Msk.filter_mask (ij_trg_mask ij) trg) (Msk.filter_mask (ij_src_mask ij) src))
      (opened : Steel.Memory.inames)
  : Steel.Effect.Atomic.SteelGhost unit opened (M.vprop_of_list trg) (fun () -> M.vprop_of_list src)
      (requires fun h0 ->
                 e'.veq_req (Msk.filter_mask_fl (ij_trg_mask ij) _ (M.sel trg h0)))
      (ensures  fun h0 () h1 ->
                 e'.veq_ens (Msk.filter_mask_fl (ij_trg_mask ij) _ (M.sel trg h0))
                            (Msk.filter_mask_fl (ij_src_mask ij) _ (M.sel src h1)) /\
                 M.veq_sel_eq (vequiv_inj_eq ij e') (M.sel trg h0) (M.sel src h1))

[@@ __cond_solver__]
let vequiv_inj
      (src : M.vprop_list) (trg : M.vprop_list)
      (ij : partial_injection src trg)
      (e' : M.vequiv (Msk.filter_mask (ij_trg_mask ij) trg) (Msk.filter_mask (ij_src_mask ij) src))
  : M.vequiv trg src
  =
    let mask_src = ij_src_mask ij in
    let mask_trg = ij_trg_mask ij in
  {
    veq_req = (fun (sl0 : M.sl_f trg) ->
                 e'.veq_req (Msk.filter_mask_fl mask_trg _ sl0));
    veq_ens = (fun (sl0 : M.sl_f trg) (sl1 : M.sl_f src) ->
                 e'.veq_ens (Msk.filter_mask_fl mask_trg _ sl0) (Msk.filter_mask_fl mask_src _ sl1));
    veq_eq  = vequiv_inj_eq  ij e';
    veq_typ = vequiv_inj_typ ij e';
    veq_g   = vequiv_inj_g   ij e';
  }

[@@__cond_solver__]
let extend_partial_injection #a (#src #trg : list a) (ij : partial_injection src trg) (src_add : list a)
  : partial_injection L.(src@src_add) trg
  =
    let f_add = L.map (fun _ -> None) src_add in
    let f = L.(ij @ f_add) in
    let src' = L.(src@src_add) in
    introduce forall (i : Fin.fin (len L.(src@src_add)) {Some? (L.index f i)}).
                  i < len src /\ L.index f i == L.index ij i
      with Ll.append_index ij f_add i;
    introduce (forall (i : Fin.fin (len src')) . Some? (L.index f i) ==>
                L.index trg (Some?.v (L.index f i)) == L.index src' i) /\
              injective_on_dom #(Fin.fin (len src')) (L.index f)
      with introduce forall i . _
           with introduce Some? (L.index f i) ==> L.index trg (Some?.v (L.index f i)) == L.index src' i
           with _ . Ll.append_index src src_add i
      and ();
    f

val extend_partial_injection_src (#a : Type) (#src #trg : list a)
                                 (ij : partial_injection src trg) (src_add : list a)
  : Lemma (Msk.filter_mask (ij_src_mask (extend_partial_injection ij src_add)) L.(src@src_add)
        == L.append (Msk.filter_mask (ij_src_mask ij) src) src_add)

val extend_partial_injection_trg (#a : Type) (#src #trg : list a)
                                 (ij : partial_injection src trg) (src_add : list a)
  : Lemma (Msk.filter_mask (ij_trg_mask (extend_partial_injection ij src_add)) trg
        == Msk.filter_mask (ij_trg_mask ij) trg)

[@@ __cond_solver__]
let vequiv_sol_inj
      (all : bool) (src : M.vprop_list) (trg : M.vprop_list)
      (ij : partial_injection src trg)
      (e' : vequiv_sol all (Msk.filter_mask (ij_src_mask ij) src) (Msk.filter_mask (ij_trg_mask ij) trg))
  : vequiv_sol all src trg
  = match e' with
  | VeqAll src' trg' e' -> VeqAll src trg (vequiv_inj src trg ij e')
  | VeqPrt src' src_add trg' e' ->
           extend_partial_injection_src ij src_add;
           extend_partial_injection_trg ij src_add;
           VeqPrt src src_add trg (vequiv_inj L.(src@src_add) trg (extend_partial_injection ij src_add) e')


(**** Tac *)

let normal_ij_mask : list norm_step = [
  delta_only [`%Msk.filter_mask; `%ij_src_mask; `%ij_trg_mask; `%L.map;
              `%None?; `%Ll.initi; `%op_Negation; `%L.mem];
  iota; zeta; primops]

/// This tactics solves a goal of the form [vequiv_sol all src trg]
let build_vequiv_sol fr ctx (all : bool) : Tac unit
  = try apply (`vequiv_sol_end)     with | _ ->
    try apply (`vequiv_sol_end_prt)
    with | _ ->
      apply_raw (`vequiv_sol_inj);
      build_partial_injection fr ctx;
      norm normal_build_partial_injection;
      norm normal_ij_mask;
    try apply (`vequiv_sol_end)     with | _ ->
    try apply (`vequiv_sol_end_prt) with | _ ->
      cs_raise fr ctx (fun m -> fail (m Fail_cond_sol []))

(*
let normal_cond_sol_to_equiv : list norm_step = [
    delta_only [`%len; `%L.length; `%L.index; `%L.op_At; `%L.append];
    delta_attr [`%__cond_solver__];
    iota; zeta; primops
  ]

let test_vequiv_sol (v : Char.char -> SE.vprop') :
   (let to_v (s : string) = L.map v (String.list_of_string s) in
    vequiv_sol false (to_v "abca") (to_v "acbdea"))
  = _ by (norm [delta_only [`%L.map]; iota; zeta; primops];
          build_vequiv_sol default_flags dummy_ctx false)    

let _ = assert (U.print_util (fun v -> vequiv_sol_prt (test_vequiv_sol v)))
            by (norm [delta_only [`%test_vequiv_sol]];
                norm normal_build_partial_injection;
                norm normal_cond_sol_to_equiv;
                fail "print")
*)

(*** Building [M.prog_cond] *)

/// The front-end tactic is [build_prog_cond], which solves a goal of the form [M.prog_cond t pre post] where
/// [t], [pre] and [post] are concrete terms (i.e. do not contain uvars).
/// Internally the main work is done by [build_tree_cond] which:
/// - solves a goal of the form [M.prog_cond t pre post] where [t] and [pre] are concrete terms but
///   [post] can be an uvar
/// - returns the shape of the program as a [pre_shape_tree]


let delayed_veq_of_list (#pre_n #post_n : nat) (l : M.veq_eq_t_list pre_n post_n) : M.veq_eq_t pre_n post_n =
  M.veq_of_list l

[@@ __cond_solver__]
let serialize_vequiv (#pre #post : M.vprop_list) (e : M.vequiv pre post) : M.vequiv pre post
  =
    let e_eq = M.veq_to_list e.veq_eq in
    { e with veq_eq = delayed_veq_of_list e_eq }

let serialize_vequiv_id (pre post : M.vprop_list) (e : M.vequiv pre post)
  : Lemma (serialize_vequiv e == e) [SMTPat (serialize_vequiv e)]
  = ()

let normal_cond_solver : list norm_step = [
    delta_only [`%len; `%None?; `%op_Negation; `%Some?.v;
                `%L.append; `%L.flatten; `%L.hd; `%L.index; `%L.length; `%L.map; `%L.mem; `%L.op_At; `%L.splitAt;
                `%L.tail; `%L.tl;
                `%Ll.initi; `%Ll.set;
                `%Perm.mk_perm_f; `%Perm.perm_f_to_list;
                `%Opt.map];
    delta_attr [`%__tac_helper__; `%__cond_solver__; `%Msk.__mask__; `%M.__vequiv__];
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
let __extract_veq_eq (#pre_n #post_n : nat) (f : Fin.fin post_n -> option (Fin.fin pre_n)) : Type
  = extract_term #(list (option int)) (Ll.initi 0 post_n
                  (fun i -> Opt.map (fun (i : Fin.fin pre_n) -> i <: int) (f i)))

[@@ __tac_helper__]
private
let __extract_vequiv (#pre #post : M.vprop_list) (e : M.vequiv pre post) : Type
  = __extract_veq_eq e.veq_eq

let tc_extract_veq_eq (n : nat) : Tac (list (option int)) =
  norm_cond_sol ();
  extract_term_tac (unquote #(list (option int)))

type pre_shape_tree : (pre_n : int) -> (post_n : int) -> Type =
  | PSspec  : (pre_n : int) -> (post_n : int) -> (pre'_n : int) -> (post'_n : int) -> (frame_n : int) ->
              (e_pre : list (option int)) -> (e_post : list (option int)) ->
              pre_shape_tree pre'_n post'_n
  | PSret   : (pre_n : int) -> (post_n : int) -> (e : list (option int)) ->
              pre_shape_tree pre_n post_n
  | PSbind  : (pre_n : int) -> (itm_n : int) -> (post_n : int) ->
              (f : pre_shape_tree pre_n itm_n) -> (g : pre_shape_tree itm_n post_n) ->
              pre_shape_tree pre_n post_n
  | PSbindP : (pre_n : int) -> (post_n : int) ->
              (g : pre_shape_tree pre_n post_n) ->
              pre_shape_tree pre_n post_n
  | PSif    : (pre_n : int) -> (post_n : int) ->
              (thn : pre_shape_tree pre_n post_n) ->
              (els : pre_shape_tree pre_n post_n) ->
              pre_shape_tree pre_n post_n

type shape_tree_t = (pre_n : nat & post_n : nat & pre_shape_tree pre_n post_n)

let rec veq_eq_list_checked_aux (pre_n : nat) (l : list (option int))
  : Tot (option (list (option (Fin.fin pre_n)))) (decreases l)
  = match l with
  | [] -> Some []
  | Some x :: xs -> if 0 <= x && x < pre_n
                  then Opt.map (Cons (Some (x <: Fin.fin pre_n))) (veq_eq_list_checked_aux pre_n xs)
                  else None
  | None   :: xs -> Opt.map (Cons None) (veq_eq_list_checked_aux pre_n xs)

let veq_eq_list_checked (pre_n : nat) (post_n : nat) (l : list (option int))
  : option (M.veq_eq_t_list pre_n post_n) =
  match veq_eq_list_checked_aux pre_n l with
  | Some r -> if L.length r = post_n then Some r else None
  | None   -> None
  

let rec shape_tree_of_pre (#pre_n : nat) (#post_n : nat) (ps : pre_shape_tree pre_n post_n)
  : Tot (option (M.shape_tree pre_n post_n)) (decreases ps)
  = match ps with
  | PSspec pre_n post_n pre'_n post'_n frame_n e_pre e_post ->
           if pre_n >= 0 && post_n >= 0 && frame_n >= 0
           then match veq_eq_list_checked pre'_n (pre_n + frame_n) e_pre,
                      veq_eq_list_checked (post_n + frame_n) post'_n e_post
           with
           | Some e0, Some e1 -> Some (M.Sspec pre_n post_n pre'_n post'_n frame_n e0 e1)
           | _ -> None
           else None
  | PSret pre_n post_n e ->
          (match veq_eq_list_checked pre_n post_n e with
          | Some e -> Some (M.Sret pre_n post_n e)
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
  | PSif pre_n post_n thn els ->
          (match shape_tree_of_pre thn, shape_tree_of_pre els with
          | Some thn, Some els -> Some (M.Sif pre_n post_n thn els)
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
      (cs0 : vequiv_sol false pre pre')

      (pre_n   : extract_term (L.length pre))
      (post_n  : (x : a) -> extract_term (L.length (post x)))
      (frame_n : extract_term (L.length (VeqPrt?.unmatched cs0)))
      (p0 : __extract_vequiv (vequiv_sol_prt cs0))

  : M.tree_cond (M.Tspec a pre post req ens) pre' (fun (x : a) -> L.(post x @ VeqPrt?.unmatched cs0))
  =
    let frame = VeqPrt?.unmatched cs0 in
    M.TCspec M.({
      tcs_pre     = pre';
      tcs_post    = (fun x -> L.(post x @ frame));
      tcs_frame   = frame;
      tcs_pre_eq  = serialize_vequiv (vequiv_sol_prt cs0);
      tcs_post_eq = (fun x -> M.vequiv_refl L.(post x @ frame))
    })

[@@ __tac_helper__]
let __build_TCspec_p
      (#a : Type) (#pre : M.pre_t) (#post : M.post_t a) (#req : M.req_t pre) (#ens : M.ens_t pre a post)
      (#pre' : M.pre_t) (#post' : M.post_t a)
      (cs0 : vequiv_sol false pre pre')
      (cs1 : (x : a) -> vequiv_sol true (post' x) L.(post x @ VeqPrt?.unmatched cs0))

      (pre_n   : extract_term (L.length pre))
      (post_n  : (x : a) -> extract_term (L.length (post x)))
      (frame_n : extract_term (L.length (VeqPrt?.unmatched cs0)))
      (p0 : __extract_vequiv (vequiv_sol_prt cs0))
      (p1 : (x : a) -> __extract_vequiv (vequiv_sol_all (cs1 x)))

  : M.tree_cond (M.Tspec a pre post req ens) pre' post'
  =
    M.TCspec M.({
      tcs_pre     = pre';
      tcs_post    = post';
      tcs_frame   = VeqPrt?.unmatched cs0;
      tcs_pre_eq  = serialize_vequiv (vequiv_sol_prt cs0);
      tcs_post_eq = (fun x -> serialize_vequiv (vequiv_sol_all (cs1 x)))
    })

// TODO? currently, one cannot factorize the tree_cond_spec part of TCspec & TCspecS
// since there are constraints on tcs_pre & tcs_post
[@@ __tac_helper__]
let __build_TCspecS_u
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (#pre' : M.pre_t)
      (tr  : M.to_repr_t a pre post req ens)
      (cs0 : vequiv_sol false tr.r_pre pre')

      (pre_n   : extract_term (L.length tr.r_pre))
      (post_n  : (x : a) -> extract_term (L.length (tr.r_post x)))
      (frame_n : extract_term (L.length (VeqPrt?.unmatched cs0)))
      (p0 : __extract_vequiv (vequiv_sol_prt cs0))

  : M.tree_cond (M.TspecS a pre post req ens) pre' (fun (x : a) -> L.(tr.r_post x @ VeqPrt?.unmatched cs0))
  =
    let frame = VeqPrt?.unmatched cs0 in
    M.TCspecS tr M.({
      tcs_pre     = pre';
      tcs_post    = (fun x -> L.(tr.r_post x @ frame));
      tcs_frame   = frame;
      tcs_pre_eq  = serialize_vequiv (vequiv_sol_prt cs0);
      tcs_post_eq = (fun x -> M.vequiv_refl L.(tr.r_post x @ frame))
    })

[@@ __tac_helper__]
let __build_TCspecS_p
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (#pre' : M.pre_t) (#post' : M.post_t a)
      (tr  : M.to_repr_t a pre post req ens)
      (cs0 : vequiv_sol false tr.r_pre pre')
      (cs1 : (x : a) -> vequiv_sol true (post' x) L.(tr.r_post x @ VeqPrt?.unmatched cs0))

      (pre_n   : extract_term (L.length tr.r_pre))
      (post_n  : (x : a) -> extract_term (L.length (tr.r_post x)))
      (frame_n : extract_term (L.length (VeqPrt?.unmatched cs0)))
      (p0 : __extract_vequiv (vequiv_sol_prt cs0))
      (p1 : (x : a) -> __extract_vequiv (vequiv_sol_all (cs1 x)))

  : M.tree_cond (M.TspecS a pre post req ens) pre' post'
  =
    M.TCspecS tr M.({
      tcs_pre     = pre';
      tcs_post    = post';
      tcs_frame   = VeqPrt?.unmatched cs0;
      tcs_pre_eq  = serialize_vequiv (vequiv_sol_prt cs0);
      tcs_post_eq = (fun x -> serialize_vequiv (vequiv_sol_all (cs1 x)))
    })


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
      (cs : vequiv_sol false (sl_hint x) pre)
      
      (n : extract_term (L.length pre))
      (p : __extract_vequiv (vequiv_sol_prt cs))

  : M.tree_cond (M.Tret a x sl_hint) pre (fun x -> L.(sl_hint x @ VeqPrt?.unmatched cs))
  =
    M.TCret pre (fun x -> L.(sl_hint x @ VeqPrt?.unmatched cs))
            (serialize_vequiv (vequiv_sol_prt cs))

[@@ __tac_helper__]
let __build_TCret_p
      (#a : Type) (#x : a) (#sl_hint : M.post_t a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (cs : vequiv_sol true (post x) pre)

      (n : extract_term (L.length pre))
      (p : __extract_vequiv (vequiv_sol_all cs))

  : M.tree_cond (M.Tret a x sl_hint) pre post
  =
    M.TCret #a #x pre post (serialize_vequiv (vequiv_sol_all cs))


let build_TCspec fr (is_Steel : bool) (post : bool) : Tac shape_tree_t
  =
    if post then begin
      if is_Steel then (
        apply_raw (`__build_TCspecS_p);
        build_to_repr_t fr (fun () -> [Info_location "in the TCspecS statement"]);
        norm_cond_sol ()
      ) else
        apply_raw (`__build_TCspec_p);
      build_vequiv_sol fr (fun () -> [Info_location "before the spec statement"]) false;
      norm_cond_sol ();
      let x = intro () in
      build_vequiv_sol fr (fun () -> [Info_location "after the spec statement"]) true
    end else begin
      // FIXME : why apply_raw shelves cs0 ?
      let cs0 = fresh_uvar None in
      if is_Steel then (
        let tr = fresh_uvar None in
        apply_raw (`(__build_TCspecS_u (`#tr) (`#cs0)));
        unshelve tr;
        build_to_repr_t fr (fun () -> [Info_location "in the TCspecS statement"]);
        unshelve cs0;
        norm_cond_sol ()
      ) else (
        apply_raw (`(__build_TCspec_u (`#cs0)));
        unshelve cs0
      );
      build_vequiv_sol fr (fun () -> [Info_location "before the spec statement"]) false
    end;

    let pre_n   = tc_extract_nat ()                     in
    let post_n  = let _ = intro () in tc_extract_nat () in
    let frame_n = tc_extract_nat ()                     in
    let pre'_n  = pre_n + frame_n                       in
    let post'_n = post_n + frame_n                      in
    let e_pre = tc_extract_veq_eq pre'_n                in
    let e_post : list (option int) =
      if post then let _ = intro () in tc_extract_veq_eq post'_n
      else Ll.initi 0 post'_n (fun i -> Some (i <: int))
    in
    (|pre'_n, post'_n, PSspec pre_n post_n pre'_n post'_n frame_n e_pre e_post|)

let build_TCret fr (post : bool) : Tac shape_tree_t
  = if post then begin
      apply_raw (`__build_TCret_p);
      build_vequiv_sol fr (fun () -> [Info_location "after the return statement"]) true
    end else begin
      let cs = fresh_uvar None in
      apply_raw (`(__build_TCret_u (`#cs)));
      unshelve cs;
      build_vequiv_sol fr (fun () -> [Info_location "after the return statement"]) false
    end;

    let n = tc_extract_nat () in
    let e = tc_extract_veq_eq n in
    (|n, n, PSret n n e|)

let rec build_TCbind fr (post : bool) : Tac shape_tree_t
  = apply (`M.TCbind);
    let (|pre_f, post_f, s_f|) = build_tree_cond fr false in
    let x = intro () in
    let (|pre_g, post_g, s_g|) = build_tree_cond fr post  in

    if post_f <> pre_g then cs_raise fr (fun () -> [Info_location "in the bind statement"])
                                    (fun m -> fail (m (Fail_shape_unification post_f pre_g) []));
    (|pre_f, post_g, PSbind pre_f post_f post_g s_f s_g|)

and build_TCbindP fr (post : bool) : Tac shape_tree_t
  = apply (`M.TCbindP);
    let x = intro () in
    let (|pre_g, post_g, s_g|) = build_tree_cond fr post in
    (|pre_g, post_g, PSbindP pre_g post_g s_g|)

/// If the post-condition of an `if` statement is not specified, it is inferred from the `then` branch.
/// Any annotation ([sl_hint] for the return) for the post-condition of the `if` should thus be on the first branch.
and build_TCif fr (post : bool) : Tac shape_tree_t
  = apply (`M.TCif);
    let (|pre_thn, post_thn, s_thn|) = build_tree_cond fr post in
    let (|pre_els, post_els, s_els|) = build_tree_cond fr true in

    let ctx () = [Info_location "in the if statement"] in
    if pre_thn  <> pre_els  then cs_raise fr ctx (fun m -> fail (m (Fail_shape_unification pre_thn pre_els) []));
    if post_thn <> post_els then cs_raise fr ctx (fun m -> fail (m (Fail_shape_unification post_thn post_els) []));
    (|pre_thn, post_thn, PSif pre_thn post_thn s_thn s_els|)

and build_tree_cond fr (post : bool) : Tac shape_tree_t
  =
    let build_tac : bool -> Tac shape_tree_t =
      let goal = cur_goal () in
      let args = (collect_app goal)._2 in
      let fail_shape () =
        cs_raise fr dummy_ctx (fun m -> fail (m (Fail_goal_shape GShape_tree_cond) [Info_goal goal])) in
      if L.length args <> 4
      then fail_shape ()
      else let hd = (collect_app (L.index args 1)._1)._1 in
      match inspect hd with
      | Tv_FVar fv ->
          // TODO? better solution to match
          let nd = inspect_fv fv in
          if Nil? nd then (let _ = fail_shape () in fail "unreachable");
          begin match L.last nd with
          | "Tspec"  -> build_TCspec  fr false
          | "TspecS" -> build_TCspec  fr true
          | "Tret"   -> build_TCret   fr
          | "Tbind"  -> build_TCbind  fr
          | "TbindP" -> build_TCbindP fr
          | "Tif"    -> build_TCif    fr
          | _ -> fail_shape ()
          end
      | _ -> fail_shape ()
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
      cs_try trefl fr dummy_ctx (fun m -> fail (m Fail_post_unification []));

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
let build_prog_cond fr : Tac unit
  = 
    let tc0   = fresh_uvar None in
    let tc_eq = fresh_uvar None in
    let ushp  = fresh_uvar None in
    apply (`(__build_prog_cond (`#tc0) (`#tc_eq) (`#ushp)));
    // [M.tree_cond t pre post]
    unshelve tc0;
    let (|pre_n, post_n, shp|) = build_tree_cond fr true in
    // tc <- tc0
    unshelve tc_eq;
    norm_cond_sol ();
    norm [delta_only [`%delayed_veq_of_list]];
    trefl ();
    // shp
    unshelve ushp;
    exact (quote shp);
    // some checks
    norm [delta_only [`%L.length; `%len]; iota; zeta; primops; simplify];
    exact (`intro_squash_l_True);
    // [shape_tree_of_pre]
    norm [delta_only [`%shape_tree_of_pre;
                      `%L.length; `%L.hd; `%L.tl; `%L.tail; `%Ll.initi; `%L.index; `%L.list_ref; `%Ll.set
                     ];
          iota; zeta; primops];
    trefl ();
    // [M.tree_cond_has_shape tc shp]
    norm [delta_only [`%M.tree_cond_has_shape; `%Perm.perm_f_to_list; `%Perm.mk_perm_f; `%Perm.mk_perm_f;
                      `%Perm.perm_f_eq; `%Perm.perm_f_of_list; `%Perm.id_n;
                      `%L.length; `%L.hd; `%L.tl; `%L.tail; `%L.index; `%L.op_At; `%L.append;
                      `%Ll.initi; `%Ll.list_eq;
                      `%Opt.opt_eq;
                      `%U.cast];
          delta_qualifier ["unfold"];
          delta_attr [`%__tac_helper__; `%M.__vequiv__];
          iota; zeta; primops; simplify];
    exact (`intro_l_True)
