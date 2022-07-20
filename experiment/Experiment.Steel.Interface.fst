module Experiment.Steel.Interface

module L = FStar.List.Pure

open FStar.Tactics


(**** Normalization attributes *)

/// Used to expose the [M.prog_tree] structure of the program.
irreducible let __repr_M__ : unit = ()

/// Normalized when building the [LV.lin_cond].
irreducible let __cond_solver__ : unit = ()

/// Normalized during the LV2SF phase.
irreducible let __LV2SF__ : unit = ()


(**** Options *)

type stage =
  | Stage_M
  | Stage_ST
  | Stage_LV : (sub_push : bool) -> stage
  | Stage_SF
  | Stage_Fun
  | Stage_WP
  | Stage_Extract

type flag =
  | No of flag
  | Timer
  | Dump of stage
  | Full_Msg
  | Extract
  | InferRO
  | WRew

noeq
type flags_record = {
  f_timer : bool;
  f_dump  : stage -> bool;
  f_flmsg : bool;
  f_extr  : bool;
  f_infRO : bool;
  f_wrew  : bool;
}

let default_flags : flags_record = {
  f_timer = false;
  f_dump  = (fun _ -> false);
  f_flmsg = false;
  f_extr  = false;
  f_infRO = true;
  f_wrew  = true;
}

let rec record_flag (pos : bool) (r : flags_record) (f : flag)
  : Tot flags_record (decreases f) =
  match f with
  | No f     -> record_flag (not pos) r f
  | Timer    -> {r with f_timer = pos}
  | Dump s   -> {r with f_dump  = (fun s' -> if s' = s then pos else r.f_dump s')}
  | Full_Msg -> {r with f_flmsg = pos}
  | Extract  -> {r with f_extr  = pos}
  | InferRO  -> {r with f_infRO = pos}
  | WRew     -> {r with f_wrew  = pos}

let make_flags_record : list flag -> flags_record =
  L.fold_left (record_flag true) default_flags


(**** Errors *)

type failure_goal_shape =
  | GShape_truth_refl_list
  | GShape_vprop
  | GShape_tree_cond
  | GShape_lin_cond
  | GShape_M_prog_tree

noeq
type failure_enum =
  | Fail_goal_shape : (expected : failure_goal_shape) -> failure_enum
  | Fail_post_unification
  | Fail_cond_sol
  | Fail_elem_index
  | Fail_shape_unification : nat -> nat -> failure_enum
  | Fail_to_repr_t
  | Fail_SMT_fallback_inj
  | Fail_eq_injection
  | Fail_pequiv_len
  | Fail_dependency : (what : string) -> (on : binder) -> failure_enum
  | Fail_csm_le
  | Fail_MRepr_implicit

noeq
type info =
  | Info_goal : typ -> info
  | Info_original_exn : exn -> info
  | Info_location : string -> info
  | Info_other : string -> info

noeq
type failure_t = {
  fail_enum : failure_enum;
  fail_info : list info
}

exception Failure of failure_t

private
let shorten_string (fr : flags_record) (s : string) : Tot string
  = if fr.f_flmsg then s
    else let idx_newl = String.index_of s '\n' in
    if 0 <= idx_newl && idx_newl < String.length s
    then String.sub s 0 idx_newl^"..."
    else s

let info_to_string (fr : flags_record) (i : info) : Tac string =
  match i with
  | Info_goal g -> "on goal: "^shorten_string fr (term_to_string g)
  | Info_original_exn exn ->
      begin match exn with
      | TacticFailure msg -> "original failure: "^shorten_string fr msg
      | exn -> "original exception: "^shorten_string fr (term_to_string (quote exn))
      end
  | Info_location s -> s
  | Info_other s -> s

let failure_enum_to_string (f : failure_enum) : Tac string =
  match f with
  | Fail_dependency what on -> "Fail_dependency: "^what^" depends on "^term_to_string (binder_to_term on)
  | _ -> let f = f in term_to_string (quote f)

private
let rec concat_sep (sep : string) (l : list string)
  : Tot string (decreases l)
  = match l with
  | []  -> ""
  | [x] -> x
  | x :: y :: tl -> x^sep^concat_sep sep (y :: tl)

let failure_to_string (fr : flags_record) (f : failure_t) : Tac string =
  concat_sep "\n" (failure_enum_to_string f.fail_enum
                  :: map (info_to_string fr) f.fail_info)
