module Learn.Option

let map #a #b (f : a -> b) (x : option a) : option b
  = match x with
  | None   -> None
  | Some x -> Some (f x)

let bind #a #b (x : option a) (f : a -> option b) : option b
  = match x with
  | None   -> None
  | Some x -> f x
