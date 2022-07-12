module Learn.Util

module T = FStar.Tactics


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

let iff_refl (a b : Type0) :
  Lemma (requires a == b) (ensures a <==> b)
  = ()

let eq2_trans #t (x z : t) (y : t) (p0 : squash (x == y)) (p1 : squash (y == z))
  : Lemma (x == z)
  = ()


/// Same as [assert_by_tactic] but returns a squash to allow [p] to be inferred
let assert_by_tac (#p : Type) (t : unit -> T.Tac unit)
  : Pure (squash p) (requires T.with_tactic t (squash p)) (ensures fun () -> True)
  = ()

/// [by_refl ()] is similar to [_ by (trefl ())] but it unfolds the local definitions
let by_refl (#a : Type) (#x #y : a) ()
  : Pure (squash (x == y)) (requires T.with_tactic T.trefl (squash (x == y))) (ensures fun () -> True)
  = ()


/// equivalent to [coerce_eq]
inline_for_extraction unfold
let cast (#a b : Type) (x : a) : Pure b (requires a == b) (ensures fun y -> y == x)
  = x

unfold
let cast_by (#a b : Type) (x : a) (pf : squash (a == b)) : Pure b (requires True) (ensures fun y -> y == x)
  = x


irreducible let __util_func__ : unit = ()

[@@ __util_func__]
let const (a #b : Type) (y : b) (_ : a)
  : b
  = y

[@@ __util_func__]
let app_on (#a : Type) (x : a) (b : Type) (f : a -> b) = f x


[@@ __util_func__]
let eta (#a:Type) (#b: a -> Type) (f: (x:a -> b x)) = fun x -> f x

[@@ __util_func__]
let eta_gtot (#a:Type) (#b: a -> Type) (f: (x:a -> GTot (b x))) = fun x -> f x

val funext_on_eta (#a : Type) (#b: a -> Type) (f g : (x:a -> b x))
                  (hp : (x:a -> squash (f x == g x)))
  : squash (eta f == eta g)

val funext_on_eta_gtot (#a : Type) (#b: a -> Type) (f g : (x:a -> GTot (b x)))
                  (hp : (x:a -> squash (f x == g x)))
  : squash (eta_gtot f == eta_gtot g)


(* TODO? automatically discharge equalities with trefl : with_tactic ? *)
let funext_eta (#a : Type) (#b : a -> Type) (f g : (x:a -> b x))
               (ef : squash (f == eta f)) (eg : squash (g == eta g))
               (eq : (x:a -> squash (f x == g x)))
  : Lemma (f == g)
  = funext_on_eta f g eq

let funext_eta_gtot (#a : Type) (#b : a -> Type) (f g : (x:a -> GTot (b x)))
               (ef : squash (f == eta_gtot f)) (eg : squash (g == eta_gtot g))
               (eq : (x:a -> squash (f x == g x)))
  : Lemma (f == g)
  = funext_on_eta_gtot f g eq

val arrow_ext
      (#a : Type) (f g : a -> Type)
      (pf : (x : a) -> squash (f x == g x))
  : squash (((x : a) -> f x) == ((x : a) -> g x))


/// [unit] for an arbitrary universe
[@@ erasable]
noeq
type unit' : Type u#a = | Unit' : unit'

/// Using [let () = block_red in t] will prevent the heuristic used for zeta-normalisation from unfolding
/// recursive functions in [t] until [block_red] is unfolded.
let block_red : unit = ()


let print_util (#a : Type) (x : a) : prop = True


type eq_dec (a : Type) = (x : a) -> (y : a) -> (b : bool {b <==> x == y})


let get_rfn (#a : Type) (#p : a -> Type) (x : a { p x })
  : Lemma (exists (r : p x) . True)
  =
    let r : squash (p x) = () in
    Squash.bind_squash #(p x) #(exists (r : p x) . True) r (fun r -> ())
