module Learn.Tactics.Util

module U = Learn.Util
module L = FStar.List.Pure

open FStar.Tactics


irreducible let __tac_helper__ : unit = ()


type timer = {
  init_ms     : int;
  start_ms    : int;
  timer_name  : string;
  timer_print : bool;
}

let timer_start (name : string) (timer_print : bool) : Tac timer =
  let init_ms = curms () in
  { init_ms; start_ms = init_ms; timer_name = name; timer_print }

let timer_stop_msg (t : timer) (end_ms : int) : Tac unit =
  print ("time "^t.timer_name^": "^string_of_int (end_ms - t.start_ms)^"ms")

let timer_stop (t : timer) : Tac unit =
  let end_ms = curms () in
  if t.timer_print
  then begin
    timer_stop_msg t end_ms;
    print ("total time : "^string_of_int (end_ms - t.init_ms)^"ms")
  end

let timer_enter (t : timer) (name : string) : Tac timer =
  let cms = curms () in
  if t.timer_print then timer_stop_msg t cms;
  { t with start_ms = cms; timer_name = name }


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


// TODO ? bv, binder, comp, attrs, match
let rec uvars_of_aux (t : term) (acc : list term) : Tac (list term) =
  match inspect t with
  | Tv_Var _ | Tv_BVar _ | Tv_FVar _ | Tv_UInst _ _ -> acc
  | Tv_App hd (arg, _) -> uvars_of_aux hd (uvars_of_aux arg acc)
  | Tv_Abs (bv:binder) body -> uvars_of_aux body acc
  | Tv_Arrow (bv:binder) (c:comp) -> acc
  | Tv_Type  _ -> acc
  | Tv_Refine (bv:bv) ref -> uvars_of_aux ref acc
  | Tv_Const  _ -> acc
  | Tv_Uvar _ _ -> t :: acc
  | Tv_Let  _ (attrs : list term) (bv:bv) def body -> uvars_of_aux def (uvars_of_aux body acc)
  | Tv_Match  scrutinee (ret:option match_returns_ascription) (brs:list branch) -> acc
  | Tv_AscribedT e t (tac:option term) _ -> uvars_of_aux e (uvars_of_aux t acc)
  | Tv_AscribedC e (c:comp) (tac:option term) _ -> uvars_of_aux e acc
  | Tv_Unknown -> acc

let uvars_of (t : term) : Tac (list term) = uvars_of_aux t []

/// The [int] argument tries to avoid inserting obvious inconsistency in the context by making each [__lax_made]
/// unique.
irreducible
let __lax_made (#a : Type) (_ : int) (f : unit -> squash False) : a
  = f ()

/// If `--lax` is set, this tactics discharges the current goal.
/// Otherwise it call [f].
let lax_guard (f : unit -> Tac unit) : Tac unit
  = if lax_on () then begin
       let mk_lax () =
         let i = fresh () in
         apply (`(__lax_made (`#(quote i))));
         let _ = intro () in smt ()
       in
       //let uvs = uvars_of (cur_goal ()) in
       mk_lax ()
       //iter (fun uv -> try unshelve uv; mk_lax () with | _ -> ()) uvs
    end else f ()


[@@ __tac_helper__]
private unfold
let __hide_squash (#p : Type u#a) (_ : unit {squash p}) : squash p
  = ()

/// With this version, the proof of the squash does not appear in the term
let squash_intro () : Tac unit =
  apply (`__hide_squash);
  refine_intro (); exact (`());
  let _ : list _ = repeatn 2 FStar.Tactics.Logic.squash_intro in ()

(*let long_proof : l_True = ()
let test : squash True = _ by ((*FStar.Tactics.Logic.*)squash_intro (); exact (`long_proof))
let _ : U.print_util test = _ by (norm [delta_only [`%test]]; fail "print")*)
