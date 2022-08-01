module Experiment.Steel.Monad

include Experiment.Steel.Interface

module M   = Experiment.Steel.Repr.M
module C   = Experiment.Steel.Combinators.Tac
module SE  = Steel.Effect
module SA  = Steel.Effect.Atomic
module SH  = Experiment.Steel.Steel
module Mem = Steel.Memory

open FStar.Tactics
open Experiment.Steel


irreducible let __monad_implicit__ : unit = ()

[@@ __repr_M__]
let return_hint (#a : Type) (#opened: Mem.inames) (x : a) (sl_hint : M.post_t a)
  : M.repr (SH.KGhostI opened) a
  = C.return_hint (SH.KGhostI opened) #a x (Some sl_hint)

[@@ __repr_M__]
let return (#a : Type) (#opened: Mem.inames) (x : a)
  : M.repr (SH.KGhostI opened) a
  = C.return (SH.KGhostI opened) #a x

[@@ __repr_M__]
let return_hint_g (#a : Type) (#opened: Mem.inames) (x : a) (sl_hint : M.post_t a)
  : M.repr (SH.KGhost opened) a
  = C.return_hint (SH.KGhost opened) #a x (Some sl_hint)

[@@ __repr_M__]
let return_g (#a : Type) (#opened: Mem.inames) (x : a)
  : M.repr (SH.KGhost opened) a
  = C.return (SH.KGhost opened) #a x

[@@ __repr_M__]
let bind
      (#a #b : Type u#a)
      (#ek0 #ek1 #ek2 : SH.effect_kind)
      (#[@@@ __monad_implicit__] cba : C.bind_combinable u#a u#p a b ek0 ek1 ek2)
      (f : M.repr ek0 a) (g : a -> M.repr ek1 b)
  : M.repr ek2 b
  = C.bind_combinable_repr cba f g

[@@ __repr_M__]
let ite
      (#a : Type) (guard : bool)
      (#ek0 #ek1 #ek2 : SH.effect_kind) 
      (#[@@@ __monad_implicit__] cba : C.ite_combinable a ek0 ek1 ek2)
      (thn : M.repr ek0 a) (els : M.repr ek1 a)
  : M.repr ek2 a
  = C.repr_lift cba.cba_ite_lift2
      (C.ite cba.cba_ite_ek2' guard
        (C.repr_lift cba.cba_ite_lift0 thn)
        (C.repr_lift cba.cba_ite_lift1 els))


/// Calling a Steel function from our representation
[@@ __repr_M__]
let call (#b : Type)
      (#a : b -> Type) (#pre : b -> SE.pre_t) (#post : (x : b) -> SE.post_t (a x))
      (#req : (x : b) -> SE.req_t (pre x)) (#ens : (x : b) -> SE.ens_t (pre x) (a x) (post x))
      ($f : (x : b) -> SE.Steel (a x) (pre x) (post x) (req x) (ens x)) (x : b)
  : M.repr SH.KSteel (a x)
  = C.repr_of_steel (pre x) (post x) (req x) (ens x) (SH.steel_fe (fun () -> f x))

[@@ __repr_M__]
let call_g (#b : Type)
      (#a : b -> Type) (#opened : b -> Mem.inames) (#pre : b -> SE.pre_t) (#post : (x : b) -> SE.post_t (a x))
      (#req : (x : b) -> SE.req_t (pre x)) (#ens : (x : b) -> SE.ens_t (pre x) (a x) (post x))
      ($f : (x : b) -> SA.SteelGhost (a x) (opened x) (pre x) (post x) (req x) (ens x)) (x : b)
  : M.repr (SH.KGhost (opened x)) (a x)
  = C.repr_of_steel (pre x) (post x) (req x) (ens x) (SH.ghost_fe (fun () -> f x))

let __assert_sq (#opened : Mem.inames) (p : Type)
  : SA.SteelGhost (squash p) opened SA.emp (fun _ -> SA.emp) (requires fun _ -> p) (ensures fun _ _ _ -> True)
  = SA.noop ()

[@@ __repr_M__]
let assert_sq (#opened : Mem.inames) (p : Type)
  : M.repr (SH.KGhost opened) (squash p)
  = call_g __assert_sq p // TODO use a spec_r_exact

/// Does not work because it requires to recheck the monotonicity of wp.
[@@ __repr_M__]
let pure (#a : Type) (#wp : pure_wp a) ($f : unit -> PURE a wp)
  : M.repr SH.KSteel a
  = C.bindP SH.KSteel wp f (fun x -> C.return SH.KSteel x)

let __ghost (#a : Type) (#opened : Mem.inames) (x : Ghost.erased a)
  : SA.SteelGhost a opened SA.emp (fun _ -> SA.emp) (fun _ -> True) (fun _ _ _ -> True)
  = SA.noop (); x

[@@ __repr_M__]
let ghost (#a : Type) (#opened : Mem.inames) (x : Ghost.erased a)
  : M.repr (SH.KGhost opened) a
  = call_g __ghost x // TODO use a spec_r_exact

/// Used when a combinator expect a specific effect. An alternative would be a bind with [noop] but this lift does
/// not change the [repr_tree].
[@@ __repr_M__]
let elift
      (#a : Type)
      (#ek0 #ek1 : SH.effect_kind) (#[@@@ __monad_implicit__] lt : C.steel_liftable a ek0 ek1)
      (f : M.repr ek0 a)
  : M.repr ek1 a
  = C.repr_lift lt f


unfold
let steel (a : Type) (pre : SE.pre_t) (post : SE.post_t a)
          (req : SE.req_t pre) (ens : SE.ens_t pre a post)
  : Type
  = SH.unit_steel a pre post req ens

let mk_steel (fs : list flag) : Tac unit
  = build_to_steel (make_flags_record fs)

/// We use the workaround of [Issue#2485](https://github.com/FStarLang/FStar/issues/2485) to call [mk_steel]
/// without retyping the generated term.
unfold
let to_steel
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (#ek0 : SH.effect_kind) (#[@@@ __monad_implicit__] lt : C.steel_liftable a ek0 SH.KSteel)
      (t : M.repr ek0 a)
      (#[exact (`(_ by (mk_steel [])))] g : __to_steel_goal a pre post req ens (C.repr_lift lt t)) ()
  : steel a pre post req ens
  = g
// TODO: other effects


[@@ resolve_implicits; __monad_implicit__]
let monad_implicits_tac () : Tac unit
  =
    let fr = default_flags in
    C.solve_combinables fr
