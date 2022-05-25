module Experiment.Steel.Notations

include Experiment.Steel.Interface

module M  = Experiment.Steel.Repr.M
module SE = Steel.Effect

open FStar.Tactics
open Experiment.Steel


unfold
let steel
  : (a : Type) -> (pre : SE.pre_t) -> (post : SE.post_t a) ->
    (req : SE.req_t pre) -> (ens : SE.ens_t pre a post) -> Type
  = M.unit_steel

unfold
let to_steel
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (t : M.repr a)
      (g : __to_steel_goal a pre post req ens t)
  : M.unit_steel a pre post req ens
  = to_steel #a #pre #post #req #ens t g

let mk_steel (fs : list flag) : Tac unit
  = build_to_steel (make_flags_record fs)


unfold
let return_hint (#a : Type) (x : a) (sl_hint : M.post_t a)
  : M.repr a
  = M.return_hint #a x sl_hint

unfold
let return (#a : Type) (x : a)
  : M.repr a
  = M.return #a x

unfold
let bind (#a #b : Type) (f : M.repr a) (g : a -> M.repr b)
  : M.repr b
  = M.bind #a #b f g

unfold
let pure (#a : Type) (#wp : pure_wp a) ($f : unit -> PURE a wp)
  : M.repr a
  = M.bindP wp f (fun x -> M.return x)

unfold
let ite (#a : Type) (guard : bool) (thn : M.repr a) (els : M.repr a)
  : M.repr a
  = M.ite guard thn els

unfold
let call (#b : Type)
      (#a : b -> Type) (#pre : b -> SE.pre_t) (#post : (x : b) -> SE.post_t (a x))
      (#req : (x : b) -> SE.req_t (pre x)) (#ens : (x : b) -> SE.ens_t (pre x) (a x) (post x))
      ($f : (x : b) -> SE.Steel (a x) (pre x) (post x) (req x) (ens x)) (x : b)
  : M.repr (a x)
  = M.repr_of_steel (pre x) (post x) (req x) (ens x) (fun () -> f x)
