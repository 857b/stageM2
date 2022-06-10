module Learn.List.Mask

module U   = Learn.Util
module Dl  = Learn.DList
module Fl  = Learn.FList
module Fin = FStar.Fin

open FStar.List.Pure
open Learn.List


irreducible let __mask__ : unit = ()

[@@__mask__]
let mask_len (mask : list bool) : nat =
  count true mask

let mask_not (#n : nat) ($mask : vec n bool) : vec n bool
  = map not mask

[@@__mask__]
let rec filter_mask (#a : Type) (#len : nat) (mask : vec len bool) (l : vec len a)
  : Tot (vec (mask_len mask) a) (decreases l)
  = match mask, l with
  | [], [] -> []
  | true  :: mask, x :: xs -> x :: filter_mask #a #(len-1) mask xs
  | false :: mask, _ :: xs -> filter_mask #a #(len-1) mask xs

[@@__mask__]
let rec mask_push (#len : nat) (mask : vec len bool) (i : Fin.fin len {index mask i})
  : Tot (Fin.fin (mask_len mask))
  =
    if i = 0 then 0
    else let b :: mask = mask in
         if b then 1 + mask_push #(len-1) mask (i-1)
         else mask_push #(len-1) mask (i - 1)

[@@__mask__]
let rec mask_pull (#len : nat) (mask : vec len bool) (j : Fin.fin (mask_len mask))
  : Tot (i : Fin.fin len {index mask i}) (decreases mask)
  = match mask with
  | true  :: mask -> if j = 0 then 0 else 1 + mask_pull #(len - 1) mask (j - 1)
  | false :: mask -> 1 + mask_pull #(len - 1) mask j

(* TODO? optimize *)
[@@__mask__]
let rec merge_fun_on_mask (#src_n : nat) (mask : vec src_n bool) (#b : Type)
      (f : (i : Fin.fin src_n {index mask i}) -> (j : Fin.fin (mask_len mask)) -> b)
      (g : (i : Fin.fin src_n {not (index mask i)}) -> b)
  : Tot (vec src_n b) (decreases mask)
  = match mask with
  | [] -> []
  | true  :: mask -> f 0 0 :: merge_fun_on_mask #(src_n-1) mask (fun i j -> f (i+1) (j+1)) (fun i -> g (i+1))
  | false :: mask -> g 0   :: merge_fun_on_mask #(src_n-1) mask (fun i j -> f (i+1)   j  ) (fun i -> g (i+1))


val merge_fun_on_mask_index (#src_n : nat) (mask : vec src_n bool) (#b : Type)
      (f : (i : Fin.fin src_n {index mask i}) -> (j : Fin.fin (mask_len mask)) -> b)
      (g : (i : Fin.fin src_n {not (index mask i)}) -> b) (i : nat)
  : Lemma (requires i < src_n)
          (ensures  index (merge_fun_on_mask #src_n mask #b f g) i ==
                   (if index mask i then f i (mask_push #src_n mask i) else g i))
          [SMTPat (index (merge_fun_on_mask #src_n mask #b f g) i)]

val mask_push_pull (#len : nat) (mask : vec len bool) (j : Fin.fin (mask_len mask))
  : Lemma (mask_push mask (mask_pull mask j) = j)
          [SMTPat (mask_push mask (mask_pull mask j))]

val mask_pull_push (#len : nat) (mask : vec len bool) (i : Fin.fin len {index mask i})
  : Lemma (mask_pull mask (mask_push mask i) = i)
          [SMTPat (mask_pull mask (mask_push mask i))]

val filter_mask_push (#len : nat) (mask : vec len bool) (i : Fin.fin len {index mask i})
                     (#a : Type) (l : vec len a)
  : Lemma (index (filter_mask mask l) (mask_push mask i) == index l i)

let filter_mask_pull (#len : nat) (mask : vec len bool) (j : Fin.fin (mask_len mask))
                     (#a : Type) (l : vec len a)
  : Lemma (index (filter_mask mask l) j == index l (mask_pull mask j))
          [SMTPat (index (filter_mask mask l) j)]
  = filter_mask_push mask (mask_pull mask j) l

val filter_mask_map (#a #b : Type) (f : a -> b) (#len : nat) (mask : vec len bool) (l : vec len a)
  : Lemma (filter_mask mask (map f l) == map f (filter_mask mask l))
          [SMTPat (filter_mask mask (map f l))]

val filter_mask_append (#a : Type) (#len #len' : nat)
      (mask : vec len bool) (mask' : vec len' bool)
      (l : vec len a) (l' : vec len' a)
  : Lemma (filter_mask #a #(len+len') (mask@mask') (l@l') == filter_mask mask l @ filter_mask mask' l')

val filter_mask_true (#a : Type) (#len : nat) (mask : vec len bool) (l : vec len a)
      (tr : (i : Fin.fin len) -> squash (index mask i))
  : Lemma (filter_mask mask l == l)


[@@__mask__]
let rec filter_mask_dl (#len : nat) (mask : vec len bool) (ts : vec len Type) (xs : Dl.dlist ts)
  : Tot (Dl.dlist (filter_mask mask ts)) (decreases ts)
  = match mask, (|ts, xs|) with
  | [], (|[], Dl.DNil|) -> Dl.DNil
  | true  :: mask, (|_ :: ts, Dl.DCons _ x _ xs|) -> Dl.DCons _ x _ (filter_mask_dl #(len-1) mask ts xs)
  | false :: mask, (|_ :: ts, Dl.DCons _ x _ xs|) -> filter_mask_dl #(len-1) mask ts xs

val filter_mask_dl_index (#len : nat) (mask : vec len bool) (ts : vec len Type) (xs : Dl.dlist ts) (i : nat)
  : Lemma (requires i < mask_len mask)
          (ensures  Dl.index (filter_mask_dl mask ts xs) i === Dl.index xs (mask_pull mask i))
          [SMTPat (Dl.index (filter_mask_dl mask ts xs) i)]

[@@__mask__]
noextract
let filter_mask_fl (#len : nat) (mask : vec len bool) (ts : vec len Type) (xs : Fl.flist ts)
  : Tot (Fl.flist (filter_mask mask ts))
  = Fl.mk_flist (filter_mask mask ts) (fun j -> filter_mask_pull mask j ts; U.cast _ (xs (mask_pull mask j)))

let filter_mask_f_dl_f (#len : nat) (mask : vec len bool) (ts : vec len Type) (xs : Fl.flist ts)
  : Lemma (Fl.flist_of_d (filter_mask_dl mask ts (Fl.dlist_of_f xs)) == filter_mask_fl mask ts xs)
  = Fl.flist_extensionality
         (filter_mask_fl mask ts xs) (Fl.flist_of_d (filter_mask_dl mask ts (Fl.dlist_of_f xs)))
         (fun i -> ())
