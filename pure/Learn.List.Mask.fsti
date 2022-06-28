module Learn.List.Mask

module U    = Learn.Util
module Dl   = Learn.DList
module Fl   = Learn.FList
module Fin  = FStar.Fin
module Perm = Learn.Permutation

open FStar.List.Pure
open Learn.List


irreducible let __mask__ : unit = ()

type mask_t (#a : Type) (l : list a) =
  vec (length l) bool

[@@__mask__]
let mask_len (mask : list bool) : nat =
  count true mask

val mask_len_le (mask : list bool) : Lemma (mask_len mask <= length mask)

[@@__mask__]
let mask_not (#n : nat) ($mask : vec n bool) : vec n bool
  = map not mask

val mask_not_len (#n : nat) ($mask : vec n bool)
  : Lemma (mask_len (mask_not mask) = n - mask_len mask)
          [SMTPat (mask_len (mask_not mask))]

[@@ __mask__]
let mask_or (#n : nat) (m0 m1 : vec n bool) : vec n bool
  = map2 ( || ) m0 m1

let mask_le (#n : nat) (m0 m1 : vec n bool)
  : prop
  = forall (i : Fin.fin n) . {:pattern (index m0 i)} index m0 i ==> index m1 i


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


[@@__mask__]
let rec mask_comp_and (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len m0) bool)
  : Pure (vec len bool) (requires True) (ensures fun m -> mask_len m = mask_len m1) (decreases m0)
  = match m0 with
  | [] -> []
  | true  :: m0 -> let hd1 :: m1 = m1 in
                 hd1 :: mask_comp_and #(len-1) m0 m1
  | false :: m0 -> false :: mask_comp_and #(len-1) m0 m1

[@@__mask__]
let rec mask_comp_or (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len (mask_not m0)) bool)
  : Pure (vec len bool) (requires True) (ensures fun m -> mask_len m = mask_len m0 + mask_len m1) (decreases m0)
  = match m0 with
  | [] -> []
  | true  :: m0 -> true :: mask_comp_or #(len-1) m0 m1
  | false :: m0 -> let hd1 :: m1 = m1 in
                 hd1 :: mask_comp_or #(len-1) m0 m1

[@@__mask__]
let mask_diff (#n : nat) (m0 m1 : vec n bool)
  = filter_mask (mask_not m0) m1

[@@ __mask__]
let mask_split_l (n0 n1 : nat) : vec (n0 + n1) bool
  = repeat n0 true @ repeat n1 false


(* TODO? optimize *)
[@@__mask__]
let rec merge_fun_on_mask (#src_n : nat) (mask : vec src_n bool) (#b : Type)
      (f : (i : Fin.fin src_n {     index mask i }) -> (j : Fin.fin (mask_len            mask)) -> b)
      (g : (i : Fin.fin src_n {not (index mask i)}) -> (j : Fin.fin (mask_len (mask_not mask))) -> b)
  : Tot (vec src_n b) (decreases mask)
  = match mask with
  | [] -> []
  | true  :: mask -> f 0 0 :: merge_fun_on_mask (mask <: vec (src_n-1) bool)
                            (fun i j -> f (i+1) (j+1)) (fun i j -> g (i+1)   j  )
  | false :: mask -> g 0 0 :: merge_fun_on_mask (mask <: vec (src_n-1) bool)
                            (fun i j -> f (i+1)   j  ) (fun i j -> g (i+1) (j+1))


val merge_fun_on_mask_index (#src_n : nat) (mask : vec src_n bool) (#b : Type)
      (f : (i : Fin.fin src_n {     index mask i }) -> (j : Fin.fin (mask_len            mask)) -> b)
      (g : (i : Fin.fin src_n {not (index mask i)}) -> (j : Fin.fin (mask_len (mask_not mask))) -> b)
      (i : nat)
  : Lemma (requires i < src_n)
          (ensures  index (merge_fun_on_mask #src_n mask #b f g) i ==
                   (if index mask i then f i (mask_push mask i) else g i (mask_push (mask_not mask) i)))
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

val filter_mask_false (#a : Type) (#len : nat) (mask : vec len bool) (l : vec len a)
      (fl : (i : Fin.fin len) -> squash (not (index mask i)))
  : Lemma (filter_mask mask l == [])


val mask_comp_or_index
      (#len : nat)
      (m0 : vec len bool)
      (m1 : vec (mask_len (mask_not m0)) bool)
      (i : Fin.fin len)
  : Lemma (index (mask_comp_or m0 m1) i == (index m0 i || index m1 (mask_push (mask_not m0) i)))
          [SMTPat (index (mask_comp_or m0 m1) i)]

val mask_comp_and_index
      (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len m0) bool) (i : Fin.fin len)
  : Lemma (index (mask_comp_and m0 m1) i == (index m0 i && index m1 (mask_push m0 i)))
          [SMTPat (index (mask_comp_and m0 m1) i)]

val mask_pull_comp_and
      (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len m0) bool) (i : Fin.fin (mask_len (mask_comp_and m0 m1)))
  : Lemma (mask_pull (mask_comp_and m0 m1) i == mask_pull m0 (mask_pull m1 i))
          [SMTPat (mask_pull (mask_comp_and m0 m1) i)]



val mask_comp_or_assoc
      (#len : nat)
      (m0 : vec len bool)
      (m1 : vec (mask_len (mask_not m0)) bool)
      (m2 : vec (mask_len (mask_not (mask_comp_or m0 m1 <: vec len bool))) bool)
  : Lemma (mask_comp_or (mask_comp_or m0 m1) m2 == mask_comp_or m0 (mask_comp_or m1 m2))

val mask_not_comp_or
      (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len (mask_not m0)) bool)
  : Lemma (mask_not (mask_comp_or m0 m1) == mask_comp_and (mask_not m0) (mask_not m1))

val filter_mask_and
      (#a : Type) (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len m0) bool) (l : vec len a)
  : Lemma (filter_mask (mask_comp_and m0 m1) l == filter_mask m1 (filter_mask m0 l))

val filter_mask_diff_map2 (#a : Type) (#n : nat) (m0 m1 : vec n bool) (l : vec n a)
  : Lemma (filter_mask (mask_diff m0 m1) (filter_mask (mask_not m0) l)
        == filter_mask (map2 (fun x y -> not x && y) m0 m1) l)

val filter_mask_diff_comm (#a : Type) (#n : nat) (m0 m1 : vec n bool) (l : vec n a)
  : Lemma (filter_mask (mask_diff m0 m1) (filter_mask (mask_not m0) l)
        == filter_mask (filter_mask m1 (mask_not m0)) (filter_mask m1 l))

val filter_mask_split_l (#a : Type) (n0 n1 : nat) (l0 : vec n0 a) (l1 : vec n1 a)
  : Lemma (filter_mask (mask_split_l n0 n1) (l0 @ l1) == l0)

val mask_or_sym (#n : nat) (m0 m1 : vec n bool)
  : Lemma (mask_or m0 m1 == mask_or m1 m0)

val mask_comp_or_mask_diff (#n : nat) (m0 m1 : vec n bool)
  : Lemma (mask_comp_or m0 (mask_diff m0 m1) == mask_or m0 m1)


#push-options "--ifuel 1 --fuel 1"

[@@__mask__]
let rec mask_perm_append (#n : nat) (m : vec n bool)
  : Tot (Perm.perm_f n)
  = match m with
  | [] ->
      U.cast _ Perm.(id_n 0)
  | true :: m ->
      let m : vec (n-1) bool = m in
      U.cast _ Perm.(perm_f_cons (mask_perm_append m))
  | false :: m ->
      let m : vec (n-1) bool = m in
      U.cast _ Perm.(comp
          (perm_f_move_head (mask_len m) (mask_len (mask_not m)))
          (U.cast _ (perm_f_cons (mask_perm_append m))))

[@@__mask__]
let rec mask_perm_append' (#n : nat) (m : vec n bool)
  : Tot (Perm.perm_f n)
  = match m with
  | [] ->
      U.cast _ Perm.(id_n 0)
  | true :: m ->
      let m : vec (n-1) bool = m in
      U.cast _ Perm.(perm_f_cons (mask_perm_append' m))
  | false :: m ->
      let m : vec (n-1) bool = m in
      U.cast _ Perm.(comp
          (U.cast _ (perm_f_cons (mask_perm_append' m)))
          (perm_f_move_to_head (mask_len m) (mask_len (mask_not m))))

[@@__mask__]
let rec mask_or_append_f (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len (mask_not m0)) bool)
  : Tot (Perm.perm_f (mask_len (mask_comp_or m0 m1))) (decreases m0)
  = match m0, m1 with
  | [], [] ->
      U.cast _ Perm.(id_n 0)
  | true :: m0, m1 ->
      let m0 : vec (len-1) bool = m0 in
      U.cast _ Perm.(perm_f_cons (mask_or_append_f #(len-1) m0 m1))
  | false :: m0, true :: m1 ->
      let m0 : vec (len-1) bool = m0 in
      U.cast _ Perm.(comp
          (perm_f_move_head (mask_len m0) (mask_len m1))
          (U.cast _ (perm_f_cons (mask_or_append_f #(len-1) m0 m1))))
  | false :: m0, false :: m1 ->
      let m0 : vec (len-1) bool = m0 in
      U.cast _ (mask_or_append_f m0 m1)
#pop-options

val mask_perm_append_inv (#n : nat) (m : vec n bool)
  : Lemma (Perm.inv_f (mask_perm_append m) == mask_perm_append' m)

// ALT? definition of mask_perm_append
val mask_perm_append'_index (#n : nat) (m : vec n bool) (i : Fin.fin n)
  : Lemma (mask_perm_append' m i == (if index m i then mask_push m i else mask_len m + mask_push (mask_not m) i))

val mask_perm_append_index (#n : nat) (m : vec n bool) (i : Fin.fin n)
  : Lemma (mask_perm_append m i ==
          (if i < mask_len m then mask_pull m i else mask_pull (mask_not m) (i - mask_len m)))

val filter_mask_perm_append (#a : Type) (#n : nat) (m : vec n bool) (l : vec n a)
  : Lemma (filter_mask m l @ filter_mask (mask_not m) l == Perm.apply_perm_r (mask_perm_append m) l)

// ALT? directly define this version
let mask_pequiv_append (#a : Type) (#n : nat) (m : vec n bool) (l : vec n a)
  : Perm.pequiv l (filter_mask m l @ filter_mask (mask_not m) l)
  =
    (**) filter_mask_perm_append m l;
    Perm.perm_cast _ (mask_perm_append m)

val filter_mask_perm_append' (#a : Type) (#n : nat) (m : vec n bool) (l : vec n a)
  : Lemma (l == Perm.apply_perm_r (mask_perm_append' m) (filter_mask m l @ filter_mask (mask_not m) l))

let mask_pequiv_append' (#a : Type) (#n : nat) (m : vec n bool) (l : vec n a)
  : Perm.pequiv (filter_mask m l @ filter_mask (mask_not m) l) l
  =
    (**) filter_mask_perm_append' m l;
    Perm.perm_cast _ (mask_perm_append' m)


val filter_mask_or_append
      (#a : Type) (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len (mask_not m0)) bool) (l : vec len a)
  : Lemma (filter_mask m0 l @ filter_mask m1 (filter_mask (mask_not m0) l)
         == Perm.apply_perm_r (mask_or_append_f m0 m1) (filter_mask (mask_comp_or m0 m1) l))

[@@__mask__]
let mask_or_pequiv_append
      (#a : Type) (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len (mask_not m0)) bool) (l : vec len a)
  : Perm.pequiv (filter_mask (mask_comp_or m0 m1) l)
                (filter_mask m0 l @ filter_mask m1 (filter_mask (mask_not m0) l))
  =
    (**) filter_mask_or_append m0 m1 l;
    Perm.perm_cast _ (mask_or_append_f m0 m1)


(*** [filter_mask_dl], [filter_mask_fl] *)

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

val filter_mask_dl_append
      (#n0 #n1 : nat) (m0 : vec n0 bool) (m1 : vec n1 bool)
      (ts0 : vec n0 Type) (ts1 : vec n1 Type)
      (xs0 : Dl.dlist ts0) (xs1 : Dl.dlist ts1)
  : Lemma (filter_mask_append m0 m1 ts0 ts1;
        filter_mask_dl #(n0 + n1) (m0 @ m1) (ts0 @ ts1) (Dl.append xs0 xs1)
     == Dl.append (filter_mask_dl m0 ts0 xs0) (filter_mask_dl m1 ts1 xs1))


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

val filter_mask_fl_perm_append (#n : nat) (m : vec n bool) (ts : vec n Type) (xs : Fl.flist ts)
  : Lemma (Fl.apply_pequiv (mask_pequiv_append m ts) xs
        == Fl.append (filter_mask_fl m ts xs) (filter_mask_fl (mask_not m) ts xs))

val filter_mask_fl_perm_append' (#n : nat) (m : vec n bool) (ts : vec n Type) (xs : Fl.flist ts)
  : Lemma (Fl.apply_pequiv (mask_pequiv_append' m ts)
                           (Fl.append (filter_mask_fl m ts xs) (filter_mask_fl (mask_not m) ts xs))
        == xs)

val filter_mask_fl_and
      (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len m0) bool) (ts : vec len Type)
      (xs : Fl.flist ts)
  : Lemma (filter_mask_and m0 m1 ts;
        filter_mask_fl (mask_comp_and m0 m1) ts xs == filter_mask_fl m1 _ (filter_mask_fl m0 ts xs))

val filter_mask_fl_append
      (#n0 #n1 : nat) (m0 : vec n0 bool) (m1 : vec n1 bool)
      (ts0 : vec n0 Type) (ts1 : vec n1 Type)
      (xs0 : Fl.flist ts0) (xs1 : Fl.flist ts1)
  : Lemma (filter_mask_append m0 m1 ts0 ts1;
        filter_mask_fl #(n0 + n1) (m0 @ m1) (ts0 @ ts1) (Fl.append xs0 xs1)
     == Fl.append (filter_mask_fl m0 ts0 xs0) (filter_mask_fl m1 ts1 xs1))
