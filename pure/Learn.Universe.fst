module Learn.Universe

irreducible let __universe__ : unit = ()

/// Redefining [FStar.Universe] in order to expose their definitions for normalisation.

type raise_t ([@@@ strictly_positive] a : Type u#a) : Type u#(max a b)
  = | RaiseVal of a

[@@ __universe__]
let raise_val (#a : Type u#a) (x : a) : raise_t u#a u#b a
  = RaiseVal x

[@@ __universe__]
let downgrade_val (#a : Type u#a) (y : raise_t u#a u#b a) : a
  = let RaiseVal x = y in x


(***** arrow *)

[@@ __universe__]
let lift_dom #a (#b : a -> Type u#c) (q : (x : a) -> b x) : (x : raise_t u#a u#b a) -> (b (downgrade_val x)) =
  fun v -> q (downgrade_val v)

[@@ __universe__]
let lift_codom (#a : Type u#c) (#b : a -> Type) (q: (x : a) -> b x) : (x : a) -> raise_t u#a u#b (b x) =
  fun v -> raise_val (q v)


(***** PURE *)

[@@ __universe__]
let raise_pure_wp' (#a : Type u#a) (wp : pure_wp' a) : pure_wp' (raise_t u#a u#b a)
  = fun pt -> wp (fun x -> pt (raise_val u#a u#b x))

[@@ __universe__]
let raise_pure_wp (#a : Type u#a) (wp : pure_wp a) : pure_wp (raise_t u#a u#b a)
  =
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    FStar.Monotonic.Pure.as_pure_wp (raise_pure_wp' #a wp)

inline_for_extraction
let raise_pure_val (#a : Type u#a) (wp : pure_wp a) (f : unit -> PURE a wp)
  : unit -> PURE (raise_t u#a u#b a) (raise_pure_wp u#a u#b wp)
  =
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    fun () -> raise_val u#a u#b (f ())

inline_for_extraction
let raise_ghost_val (#a : Type u#a) (wp : pure_wp a) (f : unit -> GHOST a wp)
  : unit -> GHOST (raise_t u#a u#b a) (raise_pure_wp u#a u#b wp)
  =
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    fun () -> raise_val u#a u#b (f ())
