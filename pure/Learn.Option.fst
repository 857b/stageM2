module Learn.Option

module U = Learn.Util
module L = FStar.List.Pure

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

let dflt #a (x : a) (y : option a) : a
  = match y with
  | Some y -> y
  | None   -> x

let rec traverse_list (#a : Type) (l : list (option a))
  : Tot (option (list a)) (decreases l)
  = match l with
  | [] -> Some []
  | (Some x) :: xs -> map (Cons x) (traverse_list xs)
  | None :: _ -> None

let rec traverse_list_length (#a : Type) (l : list (option a))
  : Lemma (requires Some? (traverse_list l)) (ensures L.length (Some?.v (traverse_list l)) == L.length l)
          [SMTPat (traverse_list l)]
  = match l with
  | [] -> ()
  | Some _ :: xs -> traverse_list_length xs

let rec traverse_list_index (#a : Type) (l : list (option a)) (i : Fin.fin (L.length l))
  : Lemma (requires Some? (traverse_list l))
          (ensures  Some? (L.index l i) /\ L.index (Some?.v (traverse_list l)) i == Some?.v (L.index l i))
  = match l with
  | [] -> ()
  | Some _ :: xs -> if i > 0 then traverse_list_index xs (i-1)
