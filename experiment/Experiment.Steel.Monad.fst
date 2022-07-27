module Experiment.Steel.Monad

include Experiment.Steel.Interface

module M   = Experiment.Steel.Repr.M
module MC  = Experiment.Steel.Combinators
module SE  = Steel.Effect
module SA  = Steel.Effect.Atomic
module SH  = Experiment.Steel.Steel
module Mem = Steel.Memory

open FStar.Tactics
open Experiment.Steel


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
      (t : M.repr SH.KSteel a)
      (#[exact (`(_ by (mk_steel [])))] g : __to_steel_goal a pre post req ens t) ()
  : steel a pre post req ens
  = to_steel #a #pre #post #req #ens t g


unfold
let return_hint (#a : Type) (x : a) (sl_hint : M.post_t a)
  : M.repr SH.KSteel a
  = MC.return_hint SH.KSteel #a x (Some sl_hint)

unfold
let return (#a : Type) (x : a)
  : M.repr SH.KSteel a
  = MC.return SH.KSteel #a x

// TODO? generalize with typeclass
unfold
let bind (#a #b : Type) (f : M.repr SH.KSteel a) (g : a -> M.repr SH.KSteel b)
  : M.repr SH.KSteel b
  = MC.bind #a #b f g

unfold
let pure (#a : Type) (#wp : pure_wp a) ($f : unit -> PURE a wp)
  : M.repr SH.KSteel a
  = MC.bindP SH.KSteel wp f (fun x -> MC.return SH.KSteel x)

unfold
let ite (#a : Type) (guard : bool) (thn : M.repr SH.KSteel a) (els : M.repr SH.KSteel a)
  : M.repr SH.KSteel a
  = MC.ite guard thn els


/// Calling a Steel function from our representation
unfold
let call (#b : Type)
      (#a : b -> Type) (#pre : b -> SE.pre_t) (#post : (x : b) -> SE.post_t (a x))
      (#req : (x : b) -> SE.req_t (pre x)) (#ens : (x : b) -> SE.ens_t (pre x) (a x) (post x))
      ($f : (x : b) -> SE.Steel (a x) (pre x) (post x) (req x) (ens x)) (x : b)
  : M.repr SH.KSteel (a x)
  = MC.repr_of_steel (pre x) (post x) (req x) (ens x) (SH.steel_fe (fun () -> f x))

unfold
let call_g (#b : Type)
      (#a : b -> Type) (#opened : b -> Mem.inames) (#pre : b -> SE.pre_t) (#post : (x : b) -> SE.post_t (a x))
      (#req : (x : b) -> SE.req_t (pre x)) (#ens : (x : b) -> SE.ens_t (pre x) (a x) (post x))
      ($f : (x : b) -> SA.SteelGhost (a x) (opened x) (pre x) (post x) (req x) (ens x)) (x : b)
  : M.repr (SH.KGhost (opened x)) (a x)
  = MC.repr_of_steel (pre x) (post x) (req x) (ens x) (SH.ghost_fe (fun () -> f x))
