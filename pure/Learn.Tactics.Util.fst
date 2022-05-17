module Learn.Tactics.Util

module L = FStar.List.Pure

open FStar.Tactics


irreducible let __tac_helper__ : unit = ()


type timer = {
  start_ms : int;
  timer_name : string;
}

let timer_start (name : string) : Tac timer =
  { start_ms = curms (); timer_name = name }

let timer_stop_msg (t : timer) (end_ms : int) : Tac unit =
  print ("time "^t.timer_name^": "^string_of_int (end_ms - t.start_ms)^"ms")

let timer_stop (t : timer) : Tac unit =
  timer_stop_msg t (curms ())

let timer_enter (t : timer) (name : string) : Tac timer =
  let cms = curms () in
  timer_stop_msg t cms;
  { start_ms = cms; timer_name = name }


[@@ __tac_helper__]
private
let __pose (goal:Type) (#t:Type) (x : t) (f : t -> goal) : goal = f x

let pose (t : term) : Tac binder =
  apply (`__pose (`#(cur_goal ())) (`#t));
  intro ()

[@@ __tac_helper__]
private
let __build (goal:Type) (t : Type) (x : t) (f : t -> goal) : goal = f x

let build (ty : term) (#r : Type) (builder : unit -> Tac r) : Tac (binder & r) =
  apply (`__build (`#(cur_goal ())) (`#ty));
  let res = builder () in
  let bd  = intro ()   in
  (bd, res)

let build_term (ty : term) (#r : Type) (builder : unit -> Tac r) : Tac (term & r) =
  let t = fresh_uvar (Some ty) in
  unshelve t;
  let res = builder () in
  (t, res)

/// try to clear each binder
let clear_all () : Tac unit =
  iter (fun bd -> try clear bd with | _ -> ()) (L.rev (cur_binders ()))

let rec repeatb (#a : Type) (t : unit -> Tac (option a)) : Tac (list a) =
  match t () with
  | Some x -> x :: repeatb t
  | None   -> []


let extract_term (#a : Type) (x : a) : Type = unit

let __extract_term_end (#a : Type) (x : a) : extract_term x = ()

/// On a goal [extract_term t], this tactics returns [f t] and solves the goal
let extract_term_tac (#a : Type) (f : term -> Tac a) : Tac a
  = let goal = cur_goal () in
    let view = inspect goal in
    match view with
    | Tv_App _ (t, Q_Explicit) ->
             let res = f t in // f is ran before solving the goal
             apply (`__extract_term_end);
             res
    | _ -> fail ("failed to extract term from "^term_to_string goal)

/// On a goal [extract_term n], this tactics returns the integer [n] and solves the goal
let extract_int_tac () : Tac int
  = extract_term_tac (fun t ->
    match inspect t with
    | Tv_Const (C_Int n) -> n
    | _ -> fail ("failed to extract int from "^term_to_string t))

/// On a goal [extract_term n], this tactics returns the natural [n] and solves the goal
let extract_nat_tac () : Tac nat
  = let n = extract_int_tac () in
    if n < 0 then fail ("extracted int "^string_of_int n^" < 0");
    n
