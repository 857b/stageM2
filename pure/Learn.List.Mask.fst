module Learn.List.Mask

module T    = FStar.Tactics
module Perm = Learn.Permutation


#push-options "--ifuel 1 --fuel 1"

let rec mask_not_len (#n : nat) ($mask : vec n bool)
  : Lemma (ensures mask_len (mask_not mask) = n - mask_len mask) (decreases n)
          [SMTPat (mask_len (mask_not mask))]
  = match mask with
  | [] -> ()
  | _ :: mask -> mask_not_len (mask <: vec (n-1) bool)

let rec merge_fun_on_mask_index #src_n mask #b f g (i : nat)
  : Lemma (requires i < src_n)
          (ensures  index (merge_fun_on_mask #src_n mask #b f g) i ==
                   (if index mask i then f i (mask_push mask i) else g i (mask_push (mask_not mask) i)))
          [SMTPat (index (merge_fun_on_mask #src_n mask #b f g) i)]
  = match mask with
  | true  :: mask ->
          let mask : vec (src_n-1) bool = mask in
          let f' (i : Fin.fin (src_n-1) {     index mask i }) (j : Fin.fin (mask_len           mask))
            = f (i + 1) (j + 1) in
          let g' (i : Fin.fin (src_n-1) {not (index mask i)}) (j : Fin.fin (mask_len (mask_not mask)))
            = g (i + 1)    j    in
          assert (merge_fun_on_mask #src_n (true :: mask) f g ==
                  f 0 0 :: merge_fun_on_mask #(src_n-1) mask f' g')
              by (T.trefl ());
          if i > 0 then merge_fun_on_mask_index #(src_n-1) mask f' g' (i - 1)
  | false :: mask ->
          let mask : vec (src_n-1) bool = mask in
          let f' (i : Fin.fin (src_n-1) {     index mask i }) (j : Fin.fin (mask_len           mask))
            = f (i + 1)    j    in
          let g' (i : Fin.fin (src_n-1) {not (index mask i)}) (j : Fin.fin (mask_len (mask_not mask)))
            = g (i + 1) (j + 1) in
          assert (merge_fun_on_mask #src_n (false :: mask) f g ==
                  g 0 0 :: merge_fun_on_mask #(src_n-1) mask f' g')
              by (T.trefl ());
          if i > 0 then merge_fun_on_mask_index #(src_n-1) mask f' g' (i - 1)

let rec mask_push_pull (#len : nat) (mask : vec len bool) (j : Fin.fin (mask_len mask))
  : Lemma (ensures mask_push mask (mask_pull mask j) = j) (decreases mask)
          [SMTPat (mask_push mask (mask_pull mask j))]
  = match mask with
  | true  :: mask -> if j = 0 then () else mask_push_pull #(len - 1) mask (j - 1)
  | false :: mask -> mask_push_pull #(len - 1) mask j

let rec mask_pull_push (#len : nat) (mask : vec len bool) (i : Fin.fin len {index mask i})
  : Lemma (ensures mask_pull mask (mask_push mask i) = i)
          [SMTPat (mask_pull mask (mask_push mask i))]
  = if i = 0 then ()
    else let b :: mask = mask in
         if b then mask_pull_push #(len-1) mask (i-1)
         else mask_pull_push #(len-1) mask  (i-1)

let rec filter_mask_push (#len : nat) (mask : vec len bool) (i : Fin.fin len {index mask i})
                         (#a : Type) (l : vec len a)
  : Lemma (ensures index (filter_mask mask l) (mask_push mask i) == index l i) (decreases l)
  = if i <> 0
    then let b :: mask = mask in
         let x :: xs   = l    in
         if b then filter_mask_push #(len-1) mask (i-1) xs
         else filter_mask_push #(len-1) mask (i - 1) xs

let filter_mask_map (#a #b : Type) (f : a -> b) (#len : nat) (mask : vec len bool) (l : vec len a)
  = list_extensionality (filter_mask mask (map f l)) (map f (filter_mask mask l)) (fun i -> ())

let rec filter_mask_append #a #len #len' mask mask' l l'
  : Lemma (ensures filter_mask #a #(len+len') (mask@mask') (l@l') == filter_mask mask l @ filter_mask mask' l')
          (decreases l)
  = match mask, l with
  | [], [] -> ()
  | b :: mask, x :: xs -> filter_mask_append #a #(len-1) mask mask' xs l'

let rec filter_mask_true (#a : Type) (#len : nat) (mask : vec len bool) (l : vec len a)
      (tr : (i : Fin.fin len) -> squash (index mask i))
  : Lemma (ensures filter_mask mask l == l) (decreases mask)
  = match mask, l with
  | [], [] -> ()
  | b :: mask, x :: xs -> tr 0; filter_mask_true #a #(len-1) mask xs (fun i -> tr (i+1))

let rec filter_mask_false (#a : Type) (#len : nat) (mask : vec len bool) (l : vec len a)
      (fl : (i : Fin.fin len) -> squash (not (index mask i)))
  : Lemma (ensures filter_mask mask l == []) (decreases mask)
  = match mask, l with
  | [], [] -> ()
  | b :: mask, x :: xs -> fl 0; filter_mask_false #a #(len-1) mask xs (fun i -> fl (i+1))


let rec mask_comp_or_index
      (#len : nat)
      (m0 : vec len bool)
      (m1 : vec (mask_len (mask_not m0)) bool)
      (i : Fin.fin len)
  : Lemma (ensures   index (mask_comp_or m0 m1) i == (index m0 i || index m1 (mask_push (mask_not m0) i)))
          (decreases len)
          [SMTPat (index (mask_comp_or m0 m1) i)]
  = match m0, m1 with
  | [], []  -> ()
  | true  :: m0, m1 | false :: m0, _  :: m1 ->
      if i > 0 then mask_comp_or_index #(len-1) m0 m1 (i-1)

let rec mask_comp_or_assoc #len m0 m1 m2
  : Lemma (ensures   mask_comp_or (mask_comp_or m0 m1) m2 == mask_comp_or m0 (mask_comp_or m1 m2))
          (decreases m0)
  = match m0, m1, m2 with
  | [], [], [] -> ()
  | true  :: m0, m1, m2 | false :: m0, true  :: m1, m2 | false :: m0, false :: m1, _ :: m2 ->
      mask_comp_or_assoc #(len-1) m0 m1 m2

let rec mask_not_comp_or #len m0 m1
  : Lemma (ensures   mask_not (mask_comp_or m0 m1) == mask_comp_and (mask_not m0) (mask_not m1))
          (decreases m0)
  = match m0, m1 with
  | [], [] -> ()
  | true :: m0, m1 | false :: m0, _ :: m1 -> mask_not_comp_or #(len-1) m0 m1

let rec filter_mask_and #a #len m0 m1 l
  : Lemma (ensures filter_mask (mask_comp_and m0 m1) l == filter_mask m1 (filter_mask m0 l))
          (decreases m0)
  = match m0, m1, l with
  | [], [], [] -> ()
  | true :: m0, _ :: m1, _ :: l | false :: m0, m1, _ :: l -> filter_mask_and #a #(len-1) m0 m1 l


let tac_filter_mask_or () : T.Tac unit = T.(
  norm [delta_only [`%mask_or_append_f]; zeta];
  norm [iota];
  norm [delta_only [`%U.cast]; iota])

#push-options "--z3rlimit 20"

let rec filter_mask_or_append
      (#a : Type) (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len (mask_not m0)) bool) (l : vec len a)
  : Tot (squash (filter_mask m0 l @ filter_mask m1 (filter_mask (mask_not m0) l)
              == Perm.apply_perm_r (mask_or_append_f m0 m1) (filter_mask (mask_comp_or m0 m1) l)))
        (decreases len)
  = match m0, m1, l with
  | [], [], [] -> ()
  | true :: m0', m1, x :: xs ->
      let m0' : vec (len-1) bool = m0'    in
      let lhs = filter_mask m0' xs @ filter_mask m1 (filter_mask (mask_not m0') xs) in
      let rhs = filter_mask (mask_comp_or m0' m1) xs in
      assert (x :: lhs == Perm.apply_perm_r (mask_or_append_f #len (true :: m0') m1) (x :: rhs))
        by T.(tac_filter_mask_or ();
              apply (`Perm.pequiv_cons_eq); smt ();
                apply (`filter_mask_or_append))
  | false :: m0', true :: m1', x :: xs ->
      let m0' : vec (len-1) bool = m0' in
      let lhs0 = filter_mask m0' xs in
      let lhs1 = filter_mask m1' (filter_mask (mask_not m0') xs) in
      let rhs  = filter_mask (mask_comp_or m0' m1') xs in
      assert (filter_mask m0 l @ filter_mask m1 (filter_mask (mask_not m0) l) == lhs0 @ x :: lhs1);
      assert (Perm.apply_perm_r (mask_or_append_f m0 m1) (filter_mask (mask_comp_or m0 m1) l)
           == Perm.apply_perm_r (mask_or_append_f #len (false :: m0') (true :: m1')) (x :: rhs));
      assert (lhs0 @ x :: lhs1 == Perm.apply_perm_r (mask_or_append_f #len (false :: m0') (true :: m1')) (x :: rhs))
        by T.(tac_filter_mask_or ();
              apply (`Perm.pequiv_trans_eq); later ();
                apply_raw (`Perm.pequiv_cons_eq); later (); later ();
                  apply_raw (`filter_mask_or_append);
                apply_raw (`Perm.pequiv_move_head_eq); later ();
              explode (); trefl (); iterAll smt)
  | false :: m0, false :: m1, x :: xs ->
      let m0 : vec (len-1) bool = m0 in
      filter_mask_or_append m0 m1 xs

(*
[@@__mask__]
let rec filter_mask_or_append
      (#a : Type) (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len (mask_not m0)) bool) (l : vec len a)
  : Tot (Perm.pequiv (filter_mask (mask_comp_or m0 m1) l)
                     (filter_mask m0 l @ filter_mask m1 (filter_mask (mask_not m0) l)))
        (decreases len)
  = match m0, m1, l with
  | [], [], [] ->
      U.cast _ (Perm.pequiv_refl #a [])
  | true :: m0, m1, x :: xs ->
      let m0 : vec (len-1) bool = m0 in
      U.cast _ (Perm.pequiv_cons x (filter_mask_or_append m0 m1 xs))
  | false :: m0, true :: m1, x :: xs ->
      let m0 : vec (len-1) bool = m0 in
      U.cast _ Perm.(pequiv_trans #_ #_ #_ #(filter_mask m0 xs @ x :: filter_mask m1 (filter_mask (mask_not m0) xs))
          (pequiv_cons x (filter_mask_or_append m0 m1 xs))
          (pequiv_move_head x (filter_mask m0 xs) (filter_mask m1 (filter_mask (mask_not m0) xs))))
  | false :: m0, false :: m1, x :: xs ->
      let m0 : vec (len-1) bool = m0 in
      U.cast _ (filter_mask_or_append m0 m1 xs)
  | _ -> false_elim () // avoids ifuel
*)

[@@__mask__]
let rec filter_mask_or_append'
      (#a : Type) (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len (mask_not m0)) bool) (l : vec len a)
  : Tot (Perm.pequiv (filter_mask m0 l @ filter_mask m1 (filter_mask (mask_not m0) l))
                     (filter_mask (mask_comp_or m0 m1) l))
        (decreases len)
  = match m0, m1, l with
  | [], [], [] ->
      U.cast _ (Perm.pequiv_refl #a [])
  | true :: m0, m1, x :: xs ->
      let m0 : vec (len-1) bool = m0 in
      U.cast _ (Perm.pequiv_cons x (filter_mask_or_append' #a #(len-1) m0 m1 xs))
  | false :: m0, true :: m1, x :: xs ->
      let m0 : vec (len-1) bool = m0 in
      U.cast _ Perm.(pequiv_trans #_ #_ #_ #(x :: filter_mask (mask_comp_or m0 m1) xs)
          (pequiv_move_to_head x (filter_mask m0 xs) (filter_mask m1 (filter_mask (mask_not m0) xs)))
          (pequiv_cons x (filter_mask_or_append' #a #(len-1) m0 m1 xs)))
  | false :: m0, false :: m1, x :: xs ->
      let m0 : vec (len-1) bool = m0 in
      U.cast _ (filter_mask_or_append' m0 m1 xs)
#pop-options


let rec filter_mask_dl_index (#len : nat) (mask : vec len bool) (ts : vec len Type) (xs : Dl.dlist ts) (i : nat)
  : Lemma (requires i < mask_len mask)
          (ensures  Dl.index (filter_mask_dl mask ts xs) i === Dl.index xs (mask_pull mask i))
          (decreases mask)
  = match mask with
  | true :: mask ->
      let t0 :: ts = ts in
      let xs = Dl.DCons?.xs xs in
      if i > 0 then filter_mask_dl_index #(len-1) mask ts xs (i - 1)
  | false :: mask ->
      let t0 :: ts = ts in
      let xs = Dl.DCons?.xs xs in
      filter_mask_dl_index #(len-1) mask ts xs i
