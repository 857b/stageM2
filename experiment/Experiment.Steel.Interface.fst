module Experiment.Steel.Interface

module L = FStar.List.Pure

open FStar.Tactics


type stage =
  | Stage_M
  | Stage_ST
  | Stage_SF
  | Stage_Fun
  | Stage_WP

type flag =
  | Timer
  | Dump of stage

noeq
type flags_record = {
  f_timer : bool;
  f_dump  : stage -> bool;
}

let default_flags : flags_record = {
  f_timer = false;
  f_dump  = (fun _ -> false);
}

let record_flag (r : flags_record) (f : flag) : flags_record =
  match f with
  | Timer  -> {r with f_timer = true}
  | Dump s -> {r with f_dump  = (fun s' -> s' = s || r.f_dump s')}

let make_flags_record : list flag -> flags_record =
  L.fold_left record_flag default_flags


type failure_goal_shape =
  | GShape_truth_refl_list
  | GShape_vprop
  | GShape_tree_cond

noeq
type failure_enum =
  | Fail_goal_shape : (expected : failure_goal_shape) -> failure_enum
  | Fail_post_unification
  | Fail_cond_sol
  | Fail_elem_index
  | Fail_shape_unification : nat -> nat -> failure_enum

noeq
type info =
  | Info_goal : typ -> info
  | Info_original_exn : exn -> info
  | Info_location : string -> info

noeq
type failure_t = {
  fail_enum : failure_enum;
  fail_info : list info
}

exception Failure of failure_t

let info_to_string (i : info) : Tac string =
  match i with
  | Info_goal g -> "on goal: "^term_to_string g
  | Info_original_exn exn ->
      begin match exn with
      | TacticFailure msg -> "original failure: "^msg
      | exn -> "original exception: "^term_to_string (quote exn)
      end
  | Info_location s -> s

private
let rec concat_sep (sep : string) (l : list string)
  : Tot string (decreases l)
  = match l with
  | []  -> ""
  | [x] -> x
  | x :: y :: tl -> x^sep^concat_sep sep (y :: tl)

let failure_to_string (f : failure_t) : Tac string =
  let enum = f.fail_enum in
  let msg = term_to_string (quote enum) in
  concat_sep "\n" (msg :: map info_to_string f.fail_info)
