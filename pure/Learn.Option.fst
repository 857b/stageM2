module Learn.Option

let bind #a #b (x : option a) (f : a -> option b) : option b
  = match x with
  | None   -> None
  | Some x -> f x
