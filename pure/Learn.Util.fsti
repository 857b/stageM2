module Learn.Util

val hide_prop : prop -> prop

val hide_propI (p : prop) : Lemma (requires p) (ensures hide_prop p)

val hide_propI_by (p : prop) (prf : unit -> Lemma (ensures p)) : Lemma (ensures hide_prop p)

val hide_propD (p : prop) : Lemma (requires hide_prop p) (ensures p)

val f_equal (#a #b : Type) (f : a -> b) (x y : a)
  : Lemma (requires x == y) (ensures f x == f y)

val prop_equal (#a : Type) (p : a -> Type) (x y : a)
  : Lemma (requires x == y /\ p x) (ensures p y)

val assert_by (p : Type) (prf : unit -> Lemma (ensures p)) : Lemma (ensures p)

unfold let alias (#t : Type) (x : t) : Type = y:t{y == x}

let cast (#a b : Type) (x : a) : Pure b (requires a == b) (ensures fun y -> y == x)
  = x
