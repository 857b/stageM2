module Demo

module US     = Learn.Steel.Util
module LList0 = Learn.Steel.List.Data
module LList1 = Learn.Steel.ListP
module DLList = Learn.Steel.DLList

module F = Experiment.Steel.Monad

open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference


//[@@handle_smt_goals]let tac () = Tactics.dump "SMT query"

let test_steel (r0 r1 : ref int)
  : Steel unit (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0      -> sel r1 h0 <= 20)
      (ensures  fun h0 _ h1 -> sel r0 h1 <= 30)
  =
    let x1 = read r1 in
    write r0 (x1 + 10)

/// [vprop]
/// Definition
/// - slprop + selector : [LList0.mlist]
/// - combinators
///   + [LList1.mlist]
///   + [DLList.dllist]
///   + [LList1.mlistN] [US.vexists]

(**** Steel VC *)

/// [Steel.Effect.bind]

(**** Functionalisation *)

/// Steel a pre post  ~~>  (sl0 : pre) -> (x : a & sl1 : post x)

let test_steel_func
      (r0 r1 : ref int) (sl0 sl1 : int)
  =
    let x1 = sl1        in
    let sl0_1 = x1 + 10 in
    (|(), sl0_1, sl1|)

//[@@handle_smt_goals]let tac () = Tactics.dump "SMT query"

noextract
let test_steel' (r0 r1 : ref int)
  : F.usteel unit (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0      -> sel r1 h0 <= 20)
      (ensures  fun h0 _ h1 -> sel r0 h1 <= 30)
  = F.(to_steel (
    x1 <-- call read r1;
    call (write r0) (x1 + 10)
  ) ())

/// [Experiment.Steel.Repr.M.prog_tree]
/// [Experiment.Steel.Repr.M.tree_cond]
/// [Experiment.Steel.Repr.LV.lin_cond]
/// [Experiment.Steel.Repr.SF.prog_tree]
/// [Experiment.Repr.Fun.prog_tree]

(***** LV *)

/// variables read-only
