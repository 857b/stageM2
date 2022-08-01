module Experiment.Steel.Combinators.Tac

include Experiment.Steel.Combinators

module U  = Learn.Util
module L  = FStar.List.Pure
module SH = Experiment.Steel.Steel

open FStar.Tactics
open Learn.Tactics.Util
open Experiment.Steel.Interface
open Experiment.Steel.Repr.M
open Experiment.Steel.Tac


(*** Lifts *)

(***** [erasable_t] *)

private unfold
let __build_revealed_value (a : Type) : (x : Ghost.erased a) -> GTot (revealed_value x)
  = fun x -> Ghost.reveal x

/// Solves a goal [erasable_t a] if a is an erasable type.
let build_erasable_t fr ctx : Tac unit
  =
    let a : term
      = match inspect (cur_goal ()) with
        | Tv_App  _ arg -> arg._1
        | _ -> fail "build_erasable_t : goal"
    in
    apply (`Mkerasable_t);
    // The following requires a conversion from [_ -> GTot (revealed_value x)] to [_ -> Tot (revealed_value x)]
    // which succeeds iff [revealed_value x] (i.e. [a]) is erasable.
    // Since we use (`#a), this may generate some guards to retypecheck (`#a).
    with_policy SMT (fun () -> cs_try (fun () ->
      exact (`(__build_revealed_value (`#a) <: _ -> Tot _)))
    fr ctx (fun m -> fail (m (Fail_not_erasable a) [])))

private
let test_erasable_unit : erasable_t unit
  = _ by (build_erasable_t default_flags dummy_ctx)

private
let test_erasable_unit' : erasable_t U.unit'
  = _ by (build_erasable_t default_flags dummy_ctx)

#push-options "--silent"
[@@ expect_failure [228]]
private
let test_erasable_int : erasable_t int
  = _ by (build_erasable_t default_flags dummy_ctx)
#pop-options

[@@ erasable]
private noeq
type test_guard_type (_ : squash (forall (n : nat) . n >= 0)) =

private
let test_erasable_guard : erasable_t (test_guard_type ())
  = _ by (build_erasable_t default_flags dummy_ctx)


(***** [steel_liftable] *)


/// Solves a goal [C.steel_liftable a ek0 ek1].
/// Since we start by trying to apply [C.Rt1n_refl], if [ek0] or [ek1] is an uvar, we will choose a trivial lift.
let rec build_steel_liftable_aux fr ctx : Tac unit
  =
    try apply (`Rt1n_refl)
    with _ ->
      apply (`Rt1n_trans);
      // lift1
      begin
        match catch (fun () -> apply (`Lift_ghost_ghostI)) with
        | Inr () -> build_erasable_t fr ctx
        | Inl _ ->
        try apply (`Lift_ghostI_atomic) with _ ->
        try apply (`Lift_atomic_steel)  with _ ->
        cs_raise fr ctx (fun m -> fail (m Fail_liftable []))
      end;

      build_steel_liftable_aux fr ctx

let build_steel_liftable fr ctx : Tac unit
  =
    let goal = cur_goal () in
    build_steel_liftable_aux fr (ctx_app_info ctx [Info_goal goal])


(*** Combinable *)

(***** [effect_kind_enum] *)

type effect_kind_enum = | ESteel | EAtomic | EGhostI | EGhost

let ek_ord (ek : effect_kind_enum) : int
  = match ek with
  | EGhost  -> 0
  | EGhostI -> 1
  | EAtomic -> 2
  | ESteel  -> 3

let ek_le (ek0 ek1 : effect_kind_enum) : bool
  = ek_ord ek0 <= ek_ord ek1

/// Given a term representing a [SH.effect_kind], returns the corresponding [effect_kind_enum].
let collect_effect_kind fr ctx (t : term) : Tac (option effect_kind_enum)
  =
    if Tv_Uvar? (inspect t) then None
    else begin
      let hd = cs_try (fun () -> collect_fvar (collect_app t)._1)
                 fr ctx (fun m -> fail (m (Fail_goal_shape GShape_effect_kind) [])) in
      Some (if hd = (`%SH.KSteel ) then ESteel
       else if hd = (`%SH.KAtomic) then EAtomic
       else if hd = (`%SH.KGhostI) then EGhostI
       else if hd = (`%SH.KGhost ) then EGhost
       else cs_raise fr ctx (fun m -> fail (m (Fail_goal_shape GShape_effect_kind) [])))
    end

/// Used to mark the definitions that have to be unfolded before collecting an [effect_kind].
irreducible let __effect_kind__ : unit = ()


(***** bind *)

[@@ __extraction__]
noeq inline_for_extraction
type bind_combinable (a0 a1 : Type u#a) (ek0 ek1 ek2 : SH.effect_kind) = {
  cba_bind_ek0'  : SH.effect_kind;
  cba_bind_ek1'  : SH.effect_kind;
  cba_bind_ek2'  : SH.effect_kind;
  cba_bind_steel : bind_steel_t u#a u#p cba_bind_ek0' cba_bind_ek1' cba_bind_ek2';
  cba_bind_lift0 : steel_liftable a0 ek0 cba_bind_ek0';
  cba_bind_lift1 : steel_liftable a1 ek1 cba_bind_ek1';
  cba_bind_lift2 : steel_liftable a1 cba_bind_ek2' ek2;
}

[@@ __repr_M__]
let bind_combinable_repr
      #a0 #a1 #ek0 #ek1 #ek2 (c : bind_combinable u#a u#p a0 a1 ek0 ek1 ek2)
      (f : repr ek0 a0) (g : a0 -> repr ek1 a1)
  : repr ek2 a1
  =
    let f' = repr_lift c.cba_bind_lift0 f              in
    let g' (x : a0) = repr_lift c.cba_bind_lift1 (g x) in
    let r' = bind_ek _ _ _ c.cba_bind_steel f' g'      in
    repr_lift c.cba_bind_lift2 r'

let bind_steel_t_for (ek0 ek1 : effect_kind_enum) : term
  = match if ek0 `ek_le` ek1 then ek1 else ek0 with
  | EGhost  -> (`bind_steel__ghost)
  | EGhostI -> (`bind_steel__ghostI)
  | EAtomic -> let ek' = if ek0 `ek_le` ek1 then ek1 else ek0 in
              if ek' `ek_le` EGhostI
              then (if ek0 = EAtomic then (`bind_steel__atomic_ghost) else (`bind_steel__ghost_atomic))
              else (`bind_steel__steel)
  | ESteel  -> (`bind_steel__steel)

/// Solves a goal [bind_combinable a0 a1 ek0' ek1' ek2'] where [ek0], [ek1] should match [ek0'], [ek1'].
let build_bind_combinable fr ctx ek0 ek1 : Tac unit
  =
    let op = bind_steel_t_for ek0 ek1 in
    apply (`Mkbind_combinable);
    // cba_bind_repr
    seq (fun () -> apply op) dismiss;
    // cba_bind_lift0
    build_steel_liftable fr ctx;
    // cba_bind_lift1
    build_steel_liftable fr ctx;
    // cba_bind_lift2
    build_steel_liftable fr ctx


(***** if-then-else *)

[@@ __extraction__]
noeq
type ite_combinable (a : Type u#a) (ek0 ek1 ek2 : SH.effect_kind) = {
  cba_ite_ek2'  : cba_ite_effect_kind_t;
  cba_ite_lift0 : steel_liftable a ek0 cba_ite_ek2';
  cba_ite_lift1 : steel_liftable a ek1 cba_ite_ek2';
  cba_ite_lift2 : steel_liftable a cba_ite_ek2' ek2;
}


[@@ __effect_kind__] let combinable_ite_ghost  o : cba_ite_effect_kind_t =  SH.KGhost  o
[@@ __effect_kind__] let combinable_ite_ghostI o : cba_ite_effect_kind_t = (SH.KGhostI o)
[@@ __effect_kind__] let combinable_ite_steel    : cba_ite_effect_kind_t =  SH.KSteel

let combinable_ite_kind (ek0 ek1 : effect_kind_enum) : term
  = match if ek0 `ek_le` ek1 then ek1 else ek0 with
  | EGhost  -> (`combinable_ite_ghost)
  | EGhostI -> (`combinable_ite_ghostI)
  | EAtomic | ESteel -> (`combinable_ite_steel)

/// Solves a goal [ite_combinable a ek0' ek1' ek2'] where [ek0], [ek1] should match [ek0'], [ek1'].
let build_ite_combinable fr ctx ek0 ek1 : Tac unit
  =
    let ek = combinable_ite_kind ek0 ek1 in
    apply_raw (`Mkite_combinable);
    // cba_ite_ek2'
    seq (fun () -> apply ek) dismiss;
    // cba_ite_lift0
    build_steel_liftable fr ctx;
    // cba_ite_lift1
    build_steel_liftable fr ctx;
    // cba_ite_lift2
    build_steel_liftable fr ctx


(*** [solve_combinables] *)

/// [solve_combinables] should be called on a state where all goals are of one of the form:
/// - [steel_liftable a ek1 ek2]
/// - [combinable_bind_t a0 a1 ek0 ek1 ek2]
/// - [combinable_ite_t a ek0 ek1 ek2]
/// It tries to solve them. It fails if it reaches a state where it cannot make progress on any goal.

/// Try to solves a goal.
/// - succeed and returns true if the heads of ek0 and ek1 are known.
/// - otherwise, returns false.
let build_combinable fr ctx : Tac bool
  =
    // there are some beta-redexes + aliases
    norm [delta_attr [`%__effect_kind__]];
    
    let hd, args = collect_app (cur_goal ()) in
    let hd = try collect_fvar hd with _ -> "unexpected shape" in
    if hd = (`%steel_liftable)
    then begin
      guard (L.length args = 3);
      let ek1 = collect_effect_kind fr ctx (L.index args 1)._1 in
      match ek1 with
      | Some _ -> build_steel_liftable fr ctx; true
      | _ -> false
    end else if hd = (`%bind_combinable)
    then begin
      guard (L.length args = 5);
      let ek0 = collect_effect_kind fr ctx (L.index args 2)._1 in
      let ek1 = collect_effect_kind fr ctx (L.index args 3)._1 in
      match ek0, ek1 with
      | Some ek0, Some ek1 -> build_bind_combinable fr ctx ek0 ek1; true
      | _ -> false
    end else if hd = (`%ite_combinable)
    then begin
      guard (L.length args = 4);
      let ek0 = collect_effect_kind fr ctx (L.index args 1)._1 in
      let ek1 = collect_effect_kind fr ctx (L.index args 2)._1 in
      match ek0, ek1 with
      | Some ek0, Some ek1 -> build_ite_combinable fr ctx ek0 ek1; true
      | _ -> false
    end else fail "build_combinable : goal_shape"

let rec solve_combinables_round fr : Tac (bool & list goal)
  = match goals () with
    | [] -> false, []
    | g :: _ ->
        if build_combinable fr dummy_ctx
        then
          let _, gs = solve_combinables_round fr in
          true, gs
        else begin
          dismiss ();
          let b, gs = solve_combinables_round fr in
          b, g :: gs
        end

let rec solve_combinables fr : Tac unit
  = match goals () with
  | [] -> ()
  | _ :: _ ->
    let b, gs = solve_combinables_round fr in
    if not b then cs_raise fr dummy_ctx (fun m -> fail (m Fail_solve_combinables []));
    set_goals gs;
    solve_combinables fr
