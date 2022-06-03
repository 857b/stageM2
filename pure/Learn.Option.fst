module Learn.Option

module U = Learn.Util

noextract
let opt_eq (#a : Type) (eq_a : U.eq_dec a) : U.eq_dec (option a)
  = fun x y -> match x, y with
  | Some x, Some y -> x `eq_a` y
  | None, None -> true
  | _ -> false

let map #a #b (f : a -> b) (x : option a) : option b
  = match x with
  | None   -> None
  | Some x -> Some (f x)

let bind #a #b (x : option a) (f : a -> option b) : option b
  = match x with
  | None   -> None
  | Some x -> f x
