module Experiment.Steel.Tac

module M    = Experiment.Steel.Repr.M
module U    = Learn.Util
module L    = FStar.List.Pure
module Ll   = Learn.List
module Fl   = Learn.FList
module Dl   = Learn.DList
module SE   = Steel.Effect
module Msk  = Learn.List.Mask
module Fin  = FStar.Fin
module Opt  = Learn.Option
module Vpl  = Experiment.Steel.VPropList
module Veq  = Experiment.Steel.VEquiv

open FStar.Tactics
open Learn.Tactics.Util
open FStar.Mul
open Experiment.Steel.Interface
open FStar.Calc


#set-options "--fuel 1 --ifuel 1"

irreducible let __cond_solver__ : unit = ()


type cs_context = unit -> list info

let dummy_ctx = fun () -> []

let ctx_app_loc (c : cs_context) (m : string) : cs_context
  = fun () -> Info_location m :: c ()

// The following utilities are hacked to raise a failure at the location where they are called
// FIXME? raise a Failure exception with a meaningful location
let cs_try (#a : Type) (f : unit -> Tac a)
           (fr : flags_record) (ctx : cs_context)
           (fail_f : (failure_enum -> list info -> Tac string) ->
                     TacH a (requires fun _ -> True) (ensures fun _ r -> Tactics.Result.Failed? r))
  : Tac a
  = try f ()
    with | e -> fail_f (fun fail_enum infos ->
                 let failure = {fail_enum; fail_info = L.(infos @ ctx () @ [Info_original_exn e])} in
                 failure_to_string fr failure)

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
  try apply (`Vpl.VeUnit) with | _ -> 
  match catch (fun () -> apply (`Vpl.VeStar)) with
  | Inr () -> build_vprop_with_emp fr ctx; (* left  *)
             build_vprop_with_emp fr ctx  (* right *)
  | Inl _ ->
  try apply (`Vpl.VeEmp ) with | _ ->
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
  delta_only [`%Vpl.flatten_vprop; `%Vpl.flatten_vprop_aux];
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
      (p : SE.vprop) (r_p : Vpl.vprop_list {p `SE.equiv` Vpl.vprop_of_list r_p}) (h : SE.rmem p)
      (v : SE.vprop{SE.can_be_split p v}) (_ : squash (SE.VUnit? v))
      (i : elem_index (SE.VUnit?._0 v) r_p)
      (i' : int) (_ : squash (i' == i))
  : squash (h v ==
        Vpl.sel r_p (SE.equiv_can_be_split p (Vpl.vprop_of_list r_p);
                   SE.focus_rmem h (Vpl.vprop_of_list r_p)) i)

[@@ __tac_helper__]
let __build_to_repr_t
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)

      (e_pre  : Vpl.vprop_with_emp pre) (r_pre  : M.pre_t)
      (pre_eq  : squash (r_pre == Vpl.flatten_vprop e_pre))

      (e_post : (x : a) -> Vpl.vprop_with_emp (post x)) (r_post : M.post_t a)
      (post_eq : (x : a) -> squash (r_post x == Vpl.flatten_vprop (e_post x)))

      (#r_req  : M.req_t r_pre)
      (r_req_eq  : (h0 : SE.rmem pre) -> (sl0 : Vpl.sl_f r_pre) ->
                   (sl0_eq : ((v : SE.vprop{SE.can_be_split pre v}) -> squash (SE.VUnit? v) ->
                             (i : elem_index (SE.VUnit?._0 v) r_pre) ->
                             // This indirection is needed so that [apply_raw] presents a goal for [i]
                             (i' : int) -> (_ : squash (i' == i)) ->
                             squash (h0 v == sl0 i'))) ->
                    r_req sl0 == req h0)

      (#r_ens  : M.ens_t r_pre a r_post)
      (r_ens_eq  : (h0 : SE.rmem pre) -> (sl0 : Vpl.sl_f r_pre) ->
                   (x : a) ->
                   (h1 : SE.rmem (post x)) -> (sl1 : Vpl.sl_f (r_post x)) ->
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
    let r_pre_eq () : Lemma (pre `SE.equiv` Vpl.vprop_of_list r_pre)
      = pre_eq;
        Vpl.vprop_equiv_flat pre e_pre;
        SE.equiv_sym (Vpl.vprop_of_list r_pre) pre in
    let r_post_eq (x : a) : Lemma (post x `SE.equiv` Vpl.vprop_of_list (r_post x))
      = post_eq x;
        Vpl.vprop_equiv_flat (post x) (e_post x);
        SE.equiv_sym (Vpl.vprop_of_list (r_post x)) (post x)
    in
    {
    r_pre; r_post; r_req; r_ens;
    r_pre_eq; r_post_eq;
    r_req_eq  = (fun (h0 : SE.rmem pre) ->
                   r_pre_eq ();
                   SE.equiv_can_be_split pre (Vpl.vprop_of_list r_pre);
                   let h0_r = SE.focus_rmem h0 (Vpl.vprop_of_list r_pre) in
                   r_req_eq h0 (Vpl.sel r_pre h0_r)
                            (__build_to_repr_t_lem pre r_pre h0));
    r_ens_eq  = (fun (h0 : SE.rmem pre) (x : a) (h1 : SE.rmem (post x)) ->
                   r_pre_eq ();
                   SE.equiv_can_be_split pre (Vpl.vprop_of_list r_pre);
                   let h0_r = SE.focus_rmem h0 (Vpl.vprop_of_list r_pre) in
                   r_post_eq x;
                   SE.equiv_can_be_split (post x) (Vpl.vprop_of_list (r_post x));
                   let h1_r = SE.focus_rmem h1 (Vpl.vprop_of_list (r_post x)) in
                   r_ens_eq h0 (Vpl.sel r_pre h0_r) x h1 (Vpl.sel (r_post x) h1_r)
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


[@@ __cond_solver__]
let rec check_injective_on_dom_aux (#b : eqtype) (f : list (option b))
  : Tot (bool & list b) (decreases f) // is injective & range
  = match f with
  | [] -> true, []
  | None :: fs   -> check_injective_on_dom_aux fs
  | Some y :: fs -> let ij, rng = check_injective_on_dom_aux fs in
                  ij && not (L.mem y rng), y :: rng

[@@ __cond_solver__]
let check_injective_on_dom (#b : eqtype) (f : list (option b))
  : bool
  = let b, _ = check_injective_on_dom_aux f in b

val check_injective_on_dom_aux_spec (#b : eqtype) (f : list (option b))
  : Lemma (let ij, rng = check_injective_on_dom_aux f in
             (ij ==> Veq.injective_on_dom #(Fin.fin (len f)) (L.index f)) /\
             (forall (y : b) . L.mem (Some y) f ==> L.mem y rng))

let check_injective_on_dom_spec (#b : eqtype) (f : list (option b))
  : Lemma (check_injective_on_dom f ==> Veq.injective_on_dom #(Fin.fin (len f)) (L.index f))
  = check_injective_on_dom_aux_spec f


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
                   Veq.injective_on_dom #(Fin.fin src_n) (L.index res)))

let build_injection_spec (#src_n #trg_n : nat) (g : ograph src_n trg_n)
  : Lemma (let res = build_injection g in
          (forall (i : Fin.fin src_n) . {:pattern (L.index res i)}
             Some? (L.index res i) ==> L.index (L.index g i) (Some?.v (L.index res i))) /\
          Veq.injective_on_dom #(Fin.fin src_n) (L.index res))
  = build_injection_iter_spec g (Ll.initi 0 trg_n (fun _ -> true))



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
  : Veq.partial_injection src trg
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
  delta_attr [`%__cond_solver__; `%__tac_helper__];
  delta_qualifier ["unfold"];
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


(***** Building an injection for smt_fallback *)

type findi_exact_r (n : nat) =
  | FER_None
  | FER_Some of (Fin.fin n)
  | FER_Err

[@@ __cond_solver__]
let rec findi_exact (#a : eqtype) (x : a) (l : list a)
  : Tot (findi_exact_r (len l))
  = match l with
  | [] -> FER_None
  | y :: ys -> match findi_exact x ys with
             | FER_None   -> if x = y then FER_Some 0 else FER_None
             | FER_Some i -> if x = y then FER_Err    else FER_Some (i+1)
             | FER_Err    -> FER_Err

[@@__cond_solver__]
let rec build_injection_exact_iter (#src_n #trg_n : nat) (g : ograph src_n trg_n)
  : Tot (option (Ll.vec src_n (option (Fin.fin trg_n)))) (decreases src_n)
  =
    match g with
    | [] -> Some []
    | im :: g ->
           let rng_t = option (Fin.fin trg_n)                     in
           let vec_cons (y : rng_t) (ys : Ll.vec (src_n-1) rng_t)
               : Ll.vec src_n rng_t = y :: ys                      in
           let ij = build_injection_exact_iter #(src_n-1) g       in
           match findi_exact true im with
           | FER_None   -> Opt.map (vec_cons (None #(Fin.fin trg_n)))   ij
           | FER_Some i -> Opt.map (vec_cons (Some #(Fin.fin trg_n) i)) ij
           | FER_Err    -> None

[@@ __cond_solver__]
let build_injection_exact (#src_n #trg_n : nat) (g : ograph src_n trg_n)
  : Tot (option (ij : Ll.vec src_n (option (Fin.fin trg_n)) {Veq.injective_on_dom #(Fin.fin src_n) (L.index ij)}))
  = Opt.bind (build_injection_exact_iter g) (fun ij ->
      if check_injective_on_dom ij
      then (check_injective_on_dom_spec ij; Some ij)
      else None #(ij : Ll.vec src_n (option (Fin.fin trg_n)) {Veq.injective_on_dom #(Fin.fin src_n) (L.index ij)}))


type key_of (#a : Type) (k : Type) (x : a) = k

[@@__tac_helper__]
private
let __intro_key_of (#a : Type) (k : Type) (x : a) (y : k) : key_of k x = y

/// Solves a goal [key_of (option string) (f xs...)] by using [Some "f"] as key if f is a FVar, [None] otherwise.
let build_key_of () : Tac unit =
  let g = cur_goal () in
  match inspect g with
  | Tv_App _ (t, Q_Explicit) ->
        let hd, _ = collect_app t in
        apply (`__intro_key_of);
       (match inspect hd with
        | Tv_FVar fv ->
              let key = implode_qn (inspect_fv fv) in
              exact (quote (Some #string key))
        | _ -> exact (quote (None #string))
        )
  | _ -> fail "build_key_of"

type key_list (#a k : Type) : list a -> Type =
  | KeyNil  : key_list #a k []
  | KeyCons : (x : a) -> (xs : list a) ->
              (y : key_of k x) -> key_list k xs ->
              key_list k (x :: xs)

/// Solves a goal [key_list string ts]
#push-options "--ifuel 2"
(**) private val __begin_opt_2 : unit
let rec build_key_list () : Tac unit =
  match catch (fun () -> apply (`KeyCons)) with
  | Inl _  -> apply (`KeyNil)
  | Inr () -> build_key_of ();
             build_key_list ()
#pop-options
(**) private val __end_opt_2 : unit


[@@__cond_solver__]
let rec extract_key_list (#a #k : Type) (#xs : list a) (l : key_list k xs)
  : Tot (l' : list k {len l' = len xs}) (decreases l)
  = match l with
  | KeyNil -> []
  | KeyCons _ _ y ys -> y :: extract_key_list ys

(*
let test_key_list (r : Steel.Reference.ref int) (v : SE.vprop')
  : key_list (option string) [Steel.Reference.vptr' r (Steel.FractionalPermission.full_perm); v]
  = _ by (build_key_list ())

let _ = fun r v -> assert (print_util (extract_key_list (test_key_list r v)))
                    by (norm [delta_only [`%test_key_list];
                              delta_attr [`%__cond_solver__; `%__tac_helper__];
                              iota; zeta]; fail "print")
*)


[@@ __cond_solver__]
let graph_of_keys (#k : Type) (f : k -> k -> bool) (src trg : list k)
  : Ll.vec (len src) (Ll.vec (len trg) bool) =
  L.map #_ #(Ll.vec (len trg) bool) (fun x -> L.map (fun y -> f x y) trg) src

[@@ __cond_solver__]
let key_eq (x x' : option string) : bool =
  match x, x' with
  | Some s, Some s' -> s = s'
  | _ -> false

type pre_partial_injection (#a : Type) (src trg : list a) =
   f : Ll.vec (len src) (option (Fin.fin (len trg)))
     { Veq.injective_on_dom #(Fin.fin (len src)) (L.index f) }

[@@__cond_solver__]
private
let __build_injection_from_key (#a : Type u#a) (src trg : list a)
      (ksrc : key_list (option string) src) (ktrg : key_list (option string) trg)
      (#ij : pre_partial_injection src trg)
      (_ : squash (Some ij ==
             build_injection_exact #(len src) #(len trg)
               (graph_of_keys key_eq (extract_key_list ksrc) (extract_key_list ktrg))))
  : pre_partial_injection src trg
  = ij

let __normal_build_injection_from_keys : list norm_step = [
  delta_only [`%L.map];
  delta_attr [`%__cond_solver__; `%__tac_helper__];
  iota; zeta
]

/// Solves a goal [pre_partial_injection src trg]
let build_pre_partial_injection_from_keys fr ctx : Tac unit
  =
    let goal = cur_goal () in
    let ij = fresh_uvar None in
    apply_raw (`__build_injection_from_key);
    // ksrc
    build_key_list ();
    // ktrg
    build_key_list ();
    // ij
    exact ij;
    // ij <- Some?.v build_injection_exact...
    norm __normal_build_injection_from_keys;
    cs_try trefl fr ctx  (fun m -> fail (m Fail_SMT_fallback_inj [Info_goal goal]))


/// The side condition encoded to the SMT for the smt_fallbacks
[@@ __cond_solver__]
let rec check_map_to_eq (#a : Type) (src trg : list a) (ij : Ll.vec (len src) (option (Fin.fin (len trg))))
  : Tot prop (decreases ij)
  = match ij with
  | [] -> True
  | None   :: ij' -> let _  :: tl = src in check_map_to_eq tl trg ij'
  | Some i :: ij' -> let hd :: tl = src in L.index trg i == hd /\ check_map_to_eq tl trg ij'

val check_map_to_eq_spec (#a : Type) (src trg : list a) (ij : Ll.vec (len src) (option (Fin.fin (len trg))))
  : Lemma (requires check_map_to_eq src trg ij) (ensures Veq.map_to_eq src trg (L.index ij))

unfold
let checked_pre_partial_injection
      (#a : Type) (#src #trg : list a) (ij : pre_partial_injection src trg)
      (_ : squash (check_map_to_eq src trg ij))
  : Veq.partial_injection src trg
  =
    (**) check_map_to_eq_spec src trg ij;
    ij
