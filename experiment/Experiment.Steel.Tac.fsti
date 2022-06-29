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
module Veq  = Experiment.Steel.VEquiv
module Perm = Learn.Permutation

open Experiment.Steel.VPropList
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


let __delta_list : list string =
  [`%L.length; `%L.index; `%L.op_At; `%L.append; `%L.map; `%L.hd; `%L.tl; `%L.tail; `%L.count; `%L.fold_left;
   `%Ll.initi; `%Ll.repeat; `%Ll.map_nth; `%Ll.set]


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
  try apply (`VeUnit) with | _ -> 
  match catch (fun () -> apply (`VeStar)) with
  | Inr () -> build_vprop_with_emp fr ctx; (* left  *)
             build_vprop_with_emp fr ctx  (* right *)
  | Inl _ ->
  try apply (`VeEmp ) with | _ ->
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
  delta_only [`%flatten_vprop; `%flatten_vprop_aux];
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
      (p : SE.vprop) (r_p : vprop_list {p `SE.equiv` vprop_of_list r_p}) (h : SE.rmem p)
      (v : SE.vprop{SE.can_be_split p v}) (_ : squash (SE.VUnit? v))
      (i : elem_index (SE.VUnit?._0 v) r_p)
      (i' : int) (_ : squash (i' == i))
  : squash (h v ==
        sel r_p (SE.equiv_can_be_split p (vprop_of_list r_p);
                   SE.focus_rmem h (vprop_of_list r_p)) i)

[@@ __tac_helper__]
let __build_to_repr_t
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)

      (e_pre  : vprop_with_emp pre) (r_pre  : M.pre_t)
      (pre_eq  : squash (r_pre == flatten_vprop e_pre))

      (e_post : (x : a) -> vprop_with_emp (post x)) (r_post : M.post_t a)
      (post_eq : (x : a) -> squash (r_post x == flatten_vprop (e_post x)))

      (#r_req  : M.req_t r_pre)
      (r_req_eq  : (h0 : SE.rmem pre) -> (sl0 : sl_f r_pre) ->
                   (sl0_eq : ((v : SE.vprop{SE.can_be_split pre v}) -> squash (SE.VUnit? v) ->
                             (i : elem_index (SE.VUnit?._0 v) r_pre) ->
                             // This indirection is needed so that [apply_raw] presents a goal for [i]
                             (i' : int) -> (_ : squash (i' == i)) ->
                             squash (h0 v == sl0 i'))) ->
                    r_req sl0 == req h0)

      (#r_ens  : M.ens_t r_pre a r_post)
      (r_ens_eq  : (h0 : SE.rmem pre) -> (sl0 : sl_f r_pre) ->
                   (x : a) ->
                   (h1 : SE.rmem (post x)) -> (sl1 : sl_f (r_post x)) ->
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
    let r_pre_eq () : Lemma (pre `SE.equiv` vprop_of_list r_pre)
      = pre_eq;
        vprop_equiv_flat pre e_pre;
        SE.equiv_sym (vprop_of_list r_pre) pre in
    let r_post_eq (x : a) : Lemma (post x `SE.equiv` vprop_of_list (r_post x))
      = post_eq x;
        vprop_equiv_flat (post x) (e_post x);
        SE.equiv_sym (vprop_of_list (r_post x)) (post x)
    in
    {
    r_pre; r_post; r_req; r_ens;
    r_pre_eq  = (fun () -> r_pre_eq (); ());
    r_post_eq = (fun x -> r_post_eq x; ());
    r_req_eq  = (fun (h0 : SE.rmem pre) ->
                   r_pre_eq ();
                   SE.equiv_can_be_split pre (vprop_of_list r_pre);
                   let h0_r = SE.focus_rmem h0 (vprop_of_list r_pre) in
                   r_req_eq h0 (sel r_pre h0_r)
                            (__build_to_repr_t_lem pre r_pre h0));
    r_ens_eq  = (fun (h0 : SE.rmem pre) (x : a) (h1 : SE.rmem (post x)) ->
                   r_pre_eq ();
                   SE.equiv_can_be_split pre (vprop_of_list r_pre);
                   let h0_r = SE.focus_rmem h0 (vprop_of_list r_pre) in
                   r_post_eq x;
                   SE.equiv_can_be_split (post x) (vprop_of_list (r_post x));
                   let h1_r = SE.focus_rmem h1 (vprop_of_list (r_post x)) in
                   r_ens_eq h0 (sel r_pre h0_r) x h1 (sel (r_post x) h1_r)
                            (__build_to_repr_t_lem pre r_pre h0)
                            (__build_to_repr_t_lem (post x) (r_post x) h1))
  }


let ctrl_rmem_apply (hs : list bv) (t : term) : Tac (bool & ctrl_flag) =
  if match inspect t with
          | Tv_App h (_v, Q_Explicit) ->
          (match inspect h with
          | Tv_Var hv -> L.existsb (fun hv' -> Order.Eq? (compare_bv hv hv')) hs
          | _ -> false) | _ -> false
  then true,  Skip
  else false, Continue

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
      let hs = [(inspect_binder h0)._1] in
      let ctrl = ctrl_rmem_apply hs in
      ctrl_rewrite TopDown ctrl
      begin fun () ->
        try apply_rew ctx_req eq0
        with _ -> trefl () // if we reach this, there will be an error in the [trefl] after the [ctrl_rewrite],
                          // but waiting to be there can give a better error dump
      end;
      cs_try trefl fr ctx_req (fun m -> fail (m Fail_to_repr_t []));

    (* [r_ens] *)
    let ctx_ens = ctx_app_loc ctx "in the ensures" in
    exact u_r_ens;
    let h0  = intro () in let sl0 = intro () in
    let x   = intro () in
    let h1  = intro () in let sl1 = intro () in
    let eq0 = intro () in let eq1 = intro () in
      norm __normal_Steel_logical_spec;
      let hs = [(inspect_binder h0)._1; (inspect_binder h1)._1] in
      let ctrl = ctrl_rmem_apply hs in
      ctrl_rewrite TopDown ctrl
      begin fun () ->
        try apply_rew ctx_ens eq0 with | _ ->
        try apply_rew ctx_ens eq1 with | _ ->
        trefl ()
      end;
      cs_try trefl fr ctx_ens (fun m -> fail (m Fail_to_repr_t []))

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


(*** Building a [spec_find_ro] *)

type sel_eq_t (pre post : vprop_list) =
    i : (Fin.fin (L.length pre) & Fin.fin (L.length post))
      { L.index pre i._1 == L.index post i._2 }

// TODO? optimize to avoid a quadratic complexity because of [( @ )]
noeq
type ens_refl (#pre #post : vprop_list) (sl0 : sl_f pre) (sl1 : sl_f post)
  : (ens : Type0) -> list (sel_eq_t pre post) -> Type
  =
  | EnsProp : (p : Type0) -> ens_refl sl0 sl1 p []
  | EnsEq   : (e : sel_eq_t pre post) ->
              (p : Type0) -> squash (p <==> (sl0 e._1 == U.cast _ (sl1 e._2))) ->
              ens_refl sl0 sl1 p [e]
  | EnsConj : (#p0 : Type0) -> (#p1 : (squash p0 -> Type0)) ->
              (#es0 : list (sel_eq_t pre post)) -> (#es1 : list (sel_eq_t pre post)) ->
              // This type for r0 reflects the laziness of [/\]
              (r0 : ens_refl sl0 sl1 p0 es0) -> (r1 : ((pf0 : squash p0) -> ens_refl sl0 sl1 (p1 pf0) es1)) ->
              ens_refl sl0 sl1 (p0 /\ p1 ()) L.(es0 @ es1)

val ens_refl_impl_eqs
      (#pre #post : vprop_list) (#sl0 : sl_f pre) (#sl1 : sl_f post)
      (#ens : Type0) (#es : list (sel_eq_t pre post))
      (r : ens_refl sl0 sl1 ens es)
      (e : sel_eq_t pre post)
  : Lemma (requires  L.memP e es /\ ens) (ensures sl0 e._1 == U.cast _ (sl1 e._2))

(* ALT to Veq.map_to_eq
type sel_eq_f (pre post : vprop_list) =
  (i_post : Ll.dom post) -> option (i_pre : Ll.dom pre {L.index pre i_pre == L.index post i_post})
 *)

let sel_eq_on
      (#pre #post : vprop_list)
      (f : Ll.dom post -> option (Ll.dom pre) { Veq.map_to_eq post pre f})
      (sl0 : sl_f pre) (sl1 : sl_f post)
  : prop
  = forall (i : Ll.dom post {Some? (f i)}) . sl0 (Some?.v (f i)) == U.cast _ (sl1 i)

/// Remove the equalities in [ens] that become redundant with [sel_eq_on f sl0 sl1].
/// Because of the dependencies (see comment), we can only replace them with [True] if there is a proposition
/// that is not eliminated somewhere on the left.
[@@ __cond_solver__]
let rec ens_refl_remove_eq_aux
      (#pre #post : vprop_list) (#sl0 : sl_f pre) (#sl1 : sl_f post)
      (#ens : Type0) (#es : list (sel_eq_t pre post))
      (r : ens_refl sl0 sl1 ens es)
      (f : Ll.dom post -> option (Ll.dom pre) { Veq.map_to_eq post pre f})
  : Pure (option Type0)
         (requires  sel_eq_on f sl0 sl1)
         (ensures   (function
                     | None -> ens
                     | Some ens' -> ens' <==> ens))
         (decreases r)
  = match r with
  | EnsProp p -> Some p
  | EnsEq e p _ ->
      if Opt.opt_eq (fun x y -> x = y) (f e._2) (Some e._1) then None else Some p
  | EnsConj #_ #_ #_ #_ #ens0 #ens1 #es0 #es1 r0 r1 ->
      let ens0'    = ens_refl_remove_eq_aux  r0     f in
      let ens1' p0 = ens_refl_remove_eq_aux (r1 p0) f in
      match ens0' with
      | None       -> ens1' ()
      | Some ens0' ->
             // the rhs of the conjunction depends on the validity of the lhs, so we cannot test if
             // it is None before introducing the [/\]
             Some (ens0' /\ (match ens1' () with | None -> True | Some ens1' -> ens1'))

[@@ __cond_solver__]
let ens_refl_remove_eq
      (#pre #post : vprop_list) (#sl0 : sl_f pre) (#sl1 : sl_f post)
      (#ens : Type0) (#es : list (sel_eq_t pre post))
      (r : ens_refl sl0 sl1 ens es)
      (f : Ll.dom post -> option (Ll.dom pre) { Veq.map_to_eq post pre f})
  : Pure Type0
         (requires sel_eq_on f sl0 sl1)
         (ensures  fun ens' -> ens' <==> ens)
  = match ens_refl_remove_eq_aux r f with
  | None      -> True
  | Some ens' -> ens'


(***** Building [ens_refl] *)

#push-options "--no_tactics"
(**) private val __begin_no_tactics : unit
[@@ __tac_helper__]
let ens_refl_rewrite_with_tactic
      (#pre #post : vprop_list) (#sl0 : sl_f pre) (#sl1 : sl_f post)
      (#t : unit -> Tac unit) (#ens : Type0) (#es : list (sel_eq_t pre post))
      (r : ens_refl sl0 sl1 ens es)
  : ens_refl sl0 sl1 (rewrite_with_tactic t ens) es
  =
    (**) unfold_rewrite_with_tactic t ens;
    r
#pop-options
(**) private val __end_no_tactics : unit

[@@ __tac_helper__]
let ens_refl_eq0
      (#pre #post : vprop_list) (#sl0 : sl_f pre) (#sl1 : sl_f post)
      (pre_i : Fin.fin (L.length pre)) (post_i : Fin.fin (L.length post)) (t : Type)
      (eq_v  : squash (let pre_v = L.index pre pre_i in
                       pre_v == L.index post post_i /\ pre_v.t == t))
  : ens_refl sl0 sl1 (eq2 #t (sl0 pre_i) (sl1 post_i)) [pre_i, post_i]
  =
    EnsEq (pre_i, post_i) (eq2 #t (sl0 pre_i) (sl1 post_i)) ()

[@@ __tac_helper__]
let ens_refl_eq1
      (#pre #post : vprop_list) (#sl0 : sl_f pre) (#sl1 : sl_f post)
      (pre_i : Fin.fin (L.length pre)) (post_i : Fin.fin (L.length post)) (t : Type)
      (eq_v  : squash (let pre_v = L.index pre pre_i in
                       pre_v == L.index post post_i /\ pre_v.t == t))
  : ens_refl sl0 sl1 (eq2 #t (sl1 post_i) (sl0 pre_i)) [pre_i, post_i]
  =
    EnsEq (pre_i, post_i) (eq2 #t (sl1 post_i) (sl0 pre_i)) ()

let __norm_index : list norm_step = [
  delta_only L.([`%index; `%hd; `%tl]);
  iota; zeta; primops
]

/// Solves a goal [ens_refl sl0 sl1 ens ?es]
let rec build_ens_refl () : Tac unit =
  try apply (`ens_refl_rewrite_with_tactic);
      build_ens_refl ()
  with _ ->
  try apply (`ens_refl_eq0);
      // eq_v
      // POTENTIALLY UNSOUND
      //   should be fine since we are only using [trefl], hence the proof does not depend on any assumptions in
      //   the context
      norm __norm_index;
      split (); trefl (); trefl ()
  with _ ->
  try apply (`ens_refl_eq1);
      // eq_v
      norm __norm_index;
      split (); trefl (); trefl ()
  with _ ->
  try apply (`EnsConj);
      // r0
      build_ens_refl ();
      // r1
      let pf0 = intro () in
      build_ens_refl ()
  with _ ->
      apply (`EnsProp)


(***** Extracting an injection *)

/// We build a partial injection from [post] to [pre], but we could probably build it in the other direction

[@@__cond_solver__]
let ograph_of_sl_eqs
      (#pre #post : vprop_list)
      (eqs : list (sel_eq_t pre post))
  : ograph (L.length post) (L.length pre)
  =
    let n_pre  = L.length pre  in
    let n_post = L.length post in
    let g0 = Ll.repeat n_post (Ll.repeat n_pre false) in
    L.fold_left (fun (g : ograph n_post n_pre) (e : sel_eq_t pre post) ->
       let i_pre, i_post = e in
       Ll.map_nth i_post (fun (c : Ll.vec n_pre bool) -> Ll.set i_pre true c) g) g0 eqs

val ograph_of_sl_eqs_spec
      (#pre #post : vprop_list)
      (eqs : list (sel_eq_t pre post))
      (i_post : Ll.dom post) (i_pre : Ll.dom pre)
  : Lemma (L.index (L.index (ograph_of_sl_eqs eqs) i_post) i_pre <==>
            (L.index pre i_pre == L.index post i_post /\ L.mem (i_pre, i_post) eqs))


(***** Splitting [pre] and [post] according to the equalities *)

val sel_eq_on_injection_iff_eq
      (#pre #post : vprop_list)
      (f : Veq.partial_injection post pre)
      (sl0 : sl_f pre) (sl1 : sl_f post)
  : Lemma (sel_eq_on (L.index f) sl0 sl1
            <==> extract_vars (Veq.ij_matched_equiv f) (filter_sl (Msk.mask_not (Veq.ij_trg_mask f)) sl0)
               == filter_sl (Msk.mask_not (Veq.ij_src_mask f)) sl1)

#push-options "--ifuel 0 --fuel 0 --z3rlimit 20"


[@@ postprocess_with (fun () -> norm [delta_qualifier ["unfold"]; iota]; trefl ())]
let build_spec_find_ro_from_vequivs__sl
      (#vs #vs' #ro : vprop_list)
      (veq : vequiv_perm L.(vs' @ ro) vs)
      (n_vs' : nat {L.length vs' == n_vs'})
      (sl : sl_f vs') (sl_fr : sl_f ro)
  : r : sl_f vs { r == (extract_vars veq (append_vars sl sl_fr)) }
  =
    let r = Fl.mk_flist (vprop_list_sels_t vs) (fun i ->
      let j = veq i in
      (**) Ll.pat_append ();
      if j < n_vs' then U.cast _ (sl j) else U.cast _ (sl_fr (j - n_vs')))
    in
    (**) Fl.flist_extensionality r (extract_vars veq (append_vars sl sl_fr)) (fun i -> ());
    r

[@@ postprocess_with (fun () -> norm [delta_only [`%build_spec_find_ro_from_vequivs__sl]]; trefl ())]
let build_spec_find_ro_from_vequivs
      (a : Type) (pre : M.pre_t) (post : M.post_t a) (req : M.req_t pre) (ens : M.ens_t pre a post)
      (spc_pre  : M.pre_t)    (n_spc_pre : nat {L.length spc_pre == n_spc_pre})
      (spc_post : M.post_t a) (n_spc_post : (x : a) -> (n : nat {L.length (spc_post x) == n}))
      (spc_ro   : vprop_list)
      (sro_pre_eq : vequiv_perm L.(spc_pre @ spc_ro) pre)
      (sro_pre_eq_eff : vequiv_perm L.(spc_pre @ spc_ro) pre {sro_pre_eq_eff == sro_pre_eq})
      (sro_post_eq : (x : a) -> vequiv_perm (post x) L.(spc_post x @ spc_ro))
      (sro_post_eq_sym : (x : a) -> (e : vequiv_perm L.(spc_post x @ spc_ro) (post x)
                                      {e == Perm.pequiv_sym (sro_post_eq x)}))
      (ens0 : M.ens_t pre a post)
      (ens_imp0 : (sl0 : sl_f pre) -> (x : a) -> (sl1 : sl_f (post x)) ->
            Lemma (requires ens sl0 x sl1)
                  (ensures  ens0 sl0 x sl1))
      (ens0_eq : (sl0 : sl_f spc_pre) -> (sl_fr0 : sl_f spc_ro) ->
                 (x : a) -> (sl1 : sl_f (spc_post x)) -> (sl_fr1 : sl_f spc_ro) ->
            Lemma (ens0 (extract_vars sro_pre_eq (append_vars sl0 sl_fr0))
                      x (extract_vars (Perm.pequiv_sym (sro_post_eq x)) (append_vars sl1 sl_fr1))
                   <==> sl_fr0 == sl_fr1))
      (ens1 : (sl0 : sl_f pre) -> (x : a) -> (sl1 : sl_f (post x)) -> squash (ens0 sl0 x sl1) -> Type0)
      (ens_eq1 : (sl0 : sl_f pre) -> (x : a) -> (sl1 : sl_f (post x)) ->
            Lemma (requires ens0 sl0 x sl1)
                  (ensures  ens sl0 x sl1 <==> ens1 sl0 x sl1 ()))
  : M.spec_find_ro a pre post req ens
  =
    let spc_ens (sl0 : sl_f spc_pre) (x : a) (sl1 : sl_f (spc_post x)) (sl_fr : sl_f spc_ro) : Type0
      =
        let sl0' = build_spec_find_ro_from_vequivs__sl  sro_pre_eq_eff      n_spc_pre     sl0 sl_fr in
        let sl1' = build_spec_find_ro_from_vequivs__sl (sro_post_eq_sym x) (n_spc_post x) sl1 sl_fr in
        ens0_eq sl0 sl_fr x sl1 sl_fr;
        assert (ens0 sl0' x sl1');
        ens1 sl0' x sl1' ()
    in
    {
    sro_spc = {
      spc_pre; spc_post; spc_ro;
      spc_req = (fun (sl0 : sl_f spc_pre) (sl_fr : sl_f spc_ro) ->
        let sl0' = build_spec_find_ro_from_vequivs__sl  sro_pre_eq_eff n_spc_pre sl0 sl_fr in
        req sl0');
      spc_ens;
    };
    sro_pre_eq; sro_post_eq;
    sro_req_eq = (fun sl0 sl_fr0 -> ());
    sro_ens_eq = (fun sl0 sl_fr0 x sl1 sl_fr1 ->
                   ens0_eq sl0 sl_fr0 x sl1 sl_fr1;
                   let sl0' = (extract_vars sro_pre_eq (append_vars sl0 sl_fr0))                        in
                   let sl1' = (extract_vars (Perm.pequiv_sym (sro_post_eq x)) (append_vars sl1 sl_fr1)) in
                   FStar.Classical.move_requires (ens_imp0 sl0' x) sl1';
                   introduce ens0 sl0' x sl1' ==> (ens sl0' x sl1' <==> ens1 sl0' x sl1' ())
                     with _ . ens_eq1  sl0' x sl1';
                   ()
                 )
  }
#pop-options


let roij_pre (#pre : vprop_list) (#n_post : nat) (ij : Ll.vec n_post (option (Ll.dom pre)))
  : vprop_list
  = Msk.(filter_mask (Veq.ij_trg_mask ij) pre)

let roij_ro (#pre : vprop_list) (#n_post : nat) (ij : Ll.vec n_post (option (Ll.dom pre)))
  : vprop_list
  = Msk.(filter_mask (mask_not (Veq.ij_trg_mask ij))) pre

let roij_post (#pre #post : vprop_list) (ij : Veq.partial_injection post pre)
  : vprop_list
  = Msk.(filter_mask (Veq.ij_src_mask ij)) post

let roij_ro' (#pre #post : vprop_list) (ij : Veq.partial_injection post pre)
  : vprop_list
  = Msk.(filter_mask (mask_not (Veq.ij_src_mask ij))) post

let roij_pre_eq (#pre : vprop_list) (#n_post : nat) (ij : Ll.vec n_post (option (Ll.dom pre)))
  : vequiv_perm L.(roij_pre ij @ roij_ro ij) pre
  = Msk.mask_pequiv_append' (Veq.ij_trg_mask ij) pre

let roij_post_eq (#pre #post : vprop_list) (ij : Veq.partial_injection post pre)
  : vequiv_perm post L.(roij_post ij @ roij_ro #pre #(L.length post) ij)
  = Perm.(
    pequiv_trans
      (Msk.mask_pequiv_append (Veq.ij_src_mask ij) post)
      (pequiv_append (pequiv_refl (roij_post ij)) (pequiv_sym (Veq.ij_matched_equiv ij))))

// ALT definition of roij_post_eq
val roij_post_eq_sym (#pre #post : vprop_list) (ij : Veq.partial_injection post pre)
  : Lemma Perm.(pequiv_sym (roij_post_eq ij) ==
                pequiv_trans
                  (pequiv_append (pequiv_refl (roij_post ij)) (Veq.ij_matched_equiv ij))
                  (Msk.mask_pequiv_append' (Veq.ij_src_mask ij) post))


/// Optimized version of [roij_pre_eq] and [roij_post_eq]

let roij_pre_eq_l (#pre : vprop_list) (#n_post : nat) (ij : Ll.vec n_post (option (Ll.dom pre)))
  : Ll.vec (L.length pre) (Ll.dom pre)
  =
    let n   = L.length pre       in
    let m1' = Veq.ij_trg_mask ij in
    let n0  = Msk.mask_len m1'   in
    (**) Msk.mask_len_le m1';
    Msk.merge_fun_on_mask m1' #(Fin.fin n)
      (fun _ j -> j)
      (fun _ j -> n0 + j)

val roij_pre_eq_l_eq (#pre : vprop_list) (#n_post : nat) (ij : Ll.vec n_post (option (Ll.dom pre)))
  : Lemma (Perm.injective (L.index (roij_pre_eq_l ij)) /\
           Perm.perm_cast _ (Perm.perm_f_of_list (roij_pre_eq_l ij)) == roij_pre_eq ij)

let roij_post_eq_l (#pre #post : vprop_list) (ij : Veq.partial_injection post pre)
  : Ll.vec (L.length post) (Ll.dom post)
  =
    let n   = L.length post      in
    let m1' = Veq.ij_src_mask ij in
    let n0  = Msk.mask_len m1'   in
    (**) Veq.ij_matched_len ij;
    Msk.merge_fun_on_mask m1' #(Fin.fin n)
      (fun _ j -> j)
      (fun _ j -> n0 + Veq.ij_matched_perm_f ij j)

val roij_post_eq_l_eq (#pre #post : vprop_list) (ij : Veq.partial_injection post pre)
  : Lemma (Perm.injective (L.index (roij_post_eq_l ij)) /\
           L.length L.(roij_post ij @ roij_ro ij) == L.length post /\
           Perm.perm_cast _ (Perm.perm_f_of_list (roij_post_eq_l ij)) == Perm.pequiv_sym (roij_post_eq ij))


val build_spec_find_ro_from_ij_lem
      (pre post : vprop_list) (ij : Veq.partial_injection post pre)
      (sl0 : sl_f (roij_pre ij)) (sl_fr0 : sl_f (roij_ro ij))
      (sl1 : sl_f (roij_post ij)) (sl_fr1 : sl_f (roij_ro #pre #(L.length post) ij))
  : Lemma (sel_eq_on (L.index ij)
                   (extract_vars (roij_pre_eq #pre #(L.length post) ij) (append_vars sl0 sl_fr0))
                   (extract_vars (Perm.pequiv_sym (roij_post_eq ij)) (append_vars sl1 sl_fr1))
             <==> sl_fr0 == sl_fr1)

let sel_eq_on_l
      (#pre #post : vprop_list)
      (f : Ll.vec (L.length post) (option (Ll.dom pre)) {Veq.map_to_eq post pre (L.index f)})
      (sl0 : sl_f pre) (sl1 : sl_f post)
  : prop
  = sel_eq_on (L.index f) sl0 sl1

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
[@@ __cond_solver__]
let build_spec_find_ro_from_ij
      (a : Type) (pre : M.pre_t) (post : M.post_t a) (req : M.req_t pre) (ens : M.ens_t pre a post)
      (ens_r_es : (x : a) -> list (sel_eq_t pre (post x)))
      (ens_r : (sl0 : sl_f pre) -> (x : a) -> (sl1 : sl_f (post x)) ->
               ens_refl sl0 sl1 (ens sl0 x sl1) (ens_r_es x))
      (n_post : nat {forall (x : a) . {:pattern (post x)} L.length (post x) = n_post})
      // ALT? [Veq.injective_on_dom] could be moved into ij_x
      (ij : Ll.vec n_post (option (Ll.dom pre)) {Veq.injective_on_dom (L.index ij)})
      (ij_x : (x : a) -> squash (
            Veq.map_to_eq (post x) pre (L.index ij) /\
            (forall (i : Fin.fin n_post {Some? (L.index ij i)}) . L.mem (Some?.v (L.index ij i), i) (ens_r_es x))))
  : M.spec_find_ro a pre post req ens
  =
    let ij' (x : a) : Veq.partial_injection (post x) pre
      = ij_x x; ij
    in
    let spc_pre          = roij_pre ij       in
    let spc_post (x : a) = roij_post (ij' x) in
    let spc_ro           = roij_ro ij        in
    let pre_eq : vequiv_perm L.(spc_pre @ spc_ro) pre
      = roij_pre_eq ij                       in
    let pre_eq_l
      = roij_pre_eq_l ij                     in
    let post_eq (x : a) : vequiv_perm (post x) L.(spc_post x @ spc_ro)
      = roij_post_eq (ij' x)                 in
    let post_eq_l (x : a)
      = roij_post_eq_l (ij' x)               in

    build_spec_find_ro_from_vequivs a pre post req ens
      spc_pre (L.length spc_pre) spc_post (fun x -> L.length (spc_post x)) spc_ro
      pre_eq  (roij_pre_eq_l_eq ij; Perm.perm_cast _ (Perm.perm_f_of_list pre_eq_l))
      post_eq (fun x -> roij_post_eq_l_eq (ij' x);
                     Perm.pequiv_as_eq (Perm.pequiv_sym (post_eq x));
                     Perm.perm_cast _ (Perm.perm_f_of_list (post_eq_l x)))
      (fun sl0 x sl1 -> ij_x x; sel_eq_on_l ij sl0 sl1)
      (fun sl0 x sl1 -> // ens_imp0
          ij_x x;
          introduce forall (i : Ll.dom (post x) {Some? (L.index ij i)}) .
                    sl0 (Some?.v (L.index ij i)) == U.cast _ (sl1 i)
          with (
            let j = Some?.v (L.index ij i) in
            assert (L.mem (j, i) (ens_r_es x));
            ens_refl_impl_eqs (ens_r sl0 x sl1) (j, i)
          ); ())
      (fun sl0 sl_fr0 x sl1 sl_fr1 -> //ens0_eq
          ij_x x;
          build_spec_find_ro_from_ij_lem pre (post x) ij sl0 sl_fr0 sl1 sl_fr1; ())
      (fun sl0 x sl1 _ -> ij_x x; ens_refl_remove_eq (ens_r sl0 x sl1) (L.index ij) <: Type0)
      (fun sl0 x sl1   -> ij_x x; ())
#pop-options

(**) private val __end_build_spec_find_ro_from_ij : unit


(***** Assembling everything *)

[@@ __cond_solver__]
let __build_spec_find_ro
      (a : Type) (pre : M.pre_t) (post : M.post_t a) (req : M.req_t pre) (ens : M.ens_t pre a post)
      (ens_r_es : (x : a) -> list (sel_eq_t pre (post x)))
      (ens_r : (sl0 : sl_f pre) -> (x : a) -> (sl1 : sl_f (post x)) ->
               ens_refl sl0 sl1 (ens sl0 x sl1) (ens_r_es x))
      (n_post : nat)
      (n_post_eq : (x : a) -> squash (L.length (post x) = n_post))
      (g : ograph n_post (L.length pre))
      (g_eq : (x : a) -> squash (n_post_eq x; g == ograph_of_sl_eqs (ens_r_es x)))
      (ij : Ll.vec n_post (option Ll.(dom pre)))
      (ij_eq : squash (ij == build_injection g))
  : M.spec_find_ro a pre post req ens
  =
    (**) FStar.Classical.forall_intro_squash_gtot n_post_eq;
    (**) build_injection_spec g;
    build_spec_find_ro_from_ij
      a pre post req ens
      ens_r_es ens_r n_post
      ij
      (fun x ->
        introduce forall (i : Fin.fin n_post {Some? (L.index ij i)}) .
                  let Some j = L.index ij i in
                  L.index pre j == L.index (post x) i /\ L.mem (j, i) (ens_r_es x)
          with begin
            let Some j = L.index ij i in
            assert (L.index (L.index g i) j);
            n_post_eq x;
            g_eq x;
            ograph_of_sl_eqs_spec (ens_r_es x) i j
          end
      )

[@@ __tac_helper__]
let __build_then_norm (#a : Type) (x : a) (y : a) (#_ : squash (y == x))
  : a
  = y

let build_then_norm_by #a #b (t : unit -> Tac a) (n : a -> Tac b) : Tac b
  =
    apply_raw (`__build_then_norm);
    // x
    let xa = t () in
    // y <- x
    dismiss ();
    let xb = n xa in
    trefl ();
    xb
    

/// Solves a goal [M.spec_find_ro a pre post req ens]
let build_spec_find_ro () : Tac unit
  =
    build_then_norm_by begin fun () ->
      apply (`__build_spec_find_ro);
      // ens_r
      let t = timer_start "ens_r" false in
      (let sl0 = intro () in
      let x   = intro () in
      let sl1 = intro () in
      build_ens_refl ());
      // n_post_eq
      let t = timer_enter t "n_post_eq" in
      (let x   = intro () in
      norm [delta_only [`%L.length]; iota; zeta];
      trefl ());
      // g_eq
      let t = timer_enter t "g_eq" in
      (let x   = intro () in
      norm [delta_only __delta_list; delta_attr [`%__cond_solver__]; iota; zeta; primops];
      trefl ());
      // ij_eq
      let t = timer_enter t "ij_eq" in
      (norm [delta_only __delta_list; delta_attr [`%__cond_solver__; `%__tac_helper__]; iota; zeta; primops];
       trefl ());
      t
    end begin fun t ->
      let t = timer_enter t "norm0" in
      norm [delta_only (L.append __delta_list
              [`%roij_pre; `%roij_post; `%roij_ro; `%roij_pre_eq_l; `%roij_post_eq_l;
               `%Veq.ij_src_mask; `%Veq.ij_trg_mask; `%Veq.mem_Some; `%Veq.ij_matched_perm; `%Veq.ij_matched_perm_f;
               `%Opt.opt_eq; `%None?; `%Some?.v;
               `%Mktuple2?._1; `%Mktuple2?._2]);
            delta_attr [`%__cond_solver__; `%__tac_helper__; `%Msk.__mask__];
            delta_qualifier ["unfold"];
            iota; zeta; primops];
      let t = timer_enter t "norm1" in
      norm [delta_only (L.append __delta_list
              [`%build_spec_find_ro_from_vequivs; `%Perm.perm_f_of_list; `%Perm.mk_perm_f;
               `%FunctionalExtensionality.on]);
            iota; zeta; primops];
      timer_stop t
    end



/// Solves a goal [sp ?s] where [sp] is as [spec_r_exact] or a [spec_r_steel]
let build_spec_r fr ctx : Tac unit =
  try apply (`M.SpecExact)
  with | _ ->
      apply_raw (`M.SpecSteel);
      build_to_repr_t fr ctx;
      norm [delta_attr [`%__tac_helper__]; iota];
      if fr.f_infRO
      then build_spec_find_ro ()
      else apply (`M.trivial_spec_find_ro)


(*** Misc *)

let match_M_prog_tree (#a : Type) fr ctx (n : name)
      (c_Tspec : a) (c_Tret : a) (c_Tbind : a) (c_TbindP : a) (c_Tif : a)
  : Tac a
  =
    let fail_shape ()
      = cs_raise fr ctx (fun m -> fail (m (Fail_goal_shape GShape_M_prog_tree)
                                       [Info_other ("got "^implode_qn n)]))
    in
    if Nil? n then fail_shape ()
    else match (L.last n) with
    | "Tspec"  -> c_Tspec
    | "Tret"   -> c_Tret
    | "Tbind"  -> c_Tbind
    | "TbindP" -> c_TbindP
    | "Tif"    -> c_Tif
    | _        -> fail_shape ()
