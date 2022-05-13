module Learn.Tactics.Util

module L = FStar.List.Pure

open FStar.Tactics


private
let __pose (goal:Type) (#t:Type) (x : t) (f : t -> goal) : goal = f x

let pose (t : term) : Tac binder =
  apply (`__pose (`#(cur_goal ())) (`#t));
  intro ()

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
