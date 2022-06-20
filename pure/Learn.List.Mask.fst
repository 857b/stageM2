module Learn.List.Mask

module Perm = Learn.Permutation

open FStar.Tactics
open FStar.List.Pure


#push-options "--ifuel 1 --fuel 1"

let rec mask_len_le (mask : list bool)
  : Lemma (ensures mask_len mask <= length mask) (decreases mask)
  = match mask with
  | [] -> ()
  | _ :: mask -> mask_len_le mask

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
              by (trefl ());
          if i > 0 then merge_fun_on_mask_index #(src_n-1) mask f' g' (i - 1)
  | false :: mask ->
          let mask : vec (src_n-1) bool = mask in
          let f' (i : Fin.fin (src_n-1) {     index mask i }) (j : Fin.fin (mask_len           mask))
            = f (i + 1)    j    in
          let g' (i : Fin.fin (src_n-1) {not (index mask i)}) (j : Fin.fin (mask_len (mask_not mask)))
            = g (i + 1) (j + 1) in
          assert (merge_fun_on_mask #src_n (false :: mask) f g ==
                  g 0 0 :: merge_fun_on_mask #(src_n-1) mask f' g')
              by (trefl ());
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

let rec mask_comp_and_index
      (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len m0) bool) (i : Fin.fin len)
  : Lemma (ensures   index (mask_comp_and m0 m1) i == (index m0 i && index m1 (mask_push m0 i)))
          (decreases len)
          [SMTPat (index (mask_comp_and m0 m1) i)]
  = match m0, m1 with
  | [], []  -> ()
  | false  :: m0, m1 | true :: m0, _  :: m1 ->
      if i > 0 then mask_comp_and_index #(len-1) m0 m1 (i-1)

let rec mask_pull_comp_and
      (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len m0) bool) (i : Fin.fin (mask_len (mask_comp_and m0 m1)))
  : Lemma (ensures   mask_pull (mask_comp_and m0 m1) i == mask_pull m0 (mask_pull m1 i))
          (decreases len)
  = match m0, m1 with
  | false  :: m0, m1 | true :: m0, false  :: m1 ->
      mask_pull_comp_and #(len-1) m0 m1 i
  | true :: m0, true  :: m1 ->
      if i > 0 then mask_pull_comp_and #(len-1) m0 m1 (i-1)


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


#push-options "--z3rlimit 20"

let rec mask_perm_append_inv (#n : nat) (m : vec n bool)
  : Lemma (ensures Perm.inv_f (mask_perm_append m) == mask_perm_append' m)
          (decreases n)
  = Perm.(match m with
  | [] -> ()
  | true :: m' ->
      let m' : vec (n-1) bool = m' in
      mask_perm_append_inv m'
  | false :: m' ->
      let m' : vec (n-1) bool = m' in
      mask_perm_append_inv m';
      let p0 = perm_cast n (perm_f_move_head (mask_len m') (mask_len (mask_not m'))) in
      let p1 = perm_cast n (perm_f_cons (mask_perm_append m')) in
      inv_f_comp p0 p1)

#push-options "--ifuel 0 --fuel 1 --z3rlimit 40"
let rec mask_perm_append'_index (#n : nat) (m : vec n bool) (i : Fin.fin n)
  : Lemma (mask_perm_append' m i == (if index m i then mask_push m i else mask_len m + mask_push (mask_not m) i))
  = match m with
  | true :: m' ->
      let m' : vec (n-1) bool = m' in
      if i > 0 then begin
        mask_perm_append'_index m' (i-1);
        assert (index m i == index m' (i-1));
        assert (mask_len m == mask_len m' + 1);
        assert (mask_perm_append' m i == mask_perm_append' m' (i-1) + 1);
        if index m i
        then assert (mask_push m i == mask_push m' (i-1) + 1)
        else assert (mask_push (mask_not m) i == mask_push (mask_not m') (i-1))
      end
  | false :: m' ->
      let m  : vec   n   bool = false :: m' in
      let m' : vec (n-1) bool = m'         in
      assert (mask_len m == mask_len m');
      if i > 0 then begin
        mask_perm_append'_index m' (i-1);
        assert (index m i == index m' (i-1));
        assert (mask_perm_append' m i
             == Perm.perm_f_move_to_head (mask_len m') (mask_len (mask_not m'))
                                              (mask_perm_append' m' (i-1) + 1));
        if index m i
        then assert (mask_push m i == mask_push m' (i-1))
        else begin
          calc (==) {
            mask_perm_append' m i;
          == { }
            Perm.perm_f_move_to_head (mask_len m') (mask_len (mask_not m'))
                          (mask_len m' + mask_push (mask_not m') (i-1) + 1);
          == { }
            mask_len m' + mask_push (mask_not m') (i-1) + 1;
          == { }
            mask_len m + mask_push (mask_not m) i;
          }
        end
      end
#pop-options

let mask_perm_append_index (#n : nat) (m : vec n bool) (i : Fin.fin n)
  : Lemma (mask_perm_append m i =
          (if i < mask_len m then mask_pull m i else mask_pull (mask_not m) (i - mask_len m)))
  =
    mask_len_le m;
    let f (i : Fin.fin n) : Fin.fin n =
      if i < mask_len m then mask_pull m i else mask_pull (mask_not m) (i - mask_len m)
    in let f' (i : Fin.fin n) : Fin.fin n =
      if index m i then mask_push m i else mask_len m + mask_push (mask_not m) i
    in
    let j = f i in
    assert (f' j == i);
    mask_perm_append'_index m j;
    mask_perm_append_inv m;
    Perm.pat_inv_f ()


let tac_filter_mask_perm_append () : Tac unit =
  norm [delta_only [`%mask_perm_append]; zeta];
  norm [iota];
  norm [delta_only [`%U.cast]; iota]

let rec filter_mask_perm_append (#a : Type) (#n : nat) (m : vec n bool) (l : vec n a)
  : Lemma (ensures   filter_mask m l @ filter_mask (mask_not m) l == Perm.apply_perm_r (mask_perm_append m) l)
          (decreases n)
  = match m, l with
  | [], [] -> ()
  | true  :: m', x :: xs ->
      let m' : vec (n-1) bool = m' in
      assert (x :: (filter_mask m' xs @ filter_mask (mask_not m') xs)
           == Perm.apply_perm_r (mask_perm_append #n (true :: m')) (x :: xs))
          by (tac_filter_mask_perm_append ();
              apply (`Perm.pequiv_cons_eq); smt ();
                apply_lemma (`filter_mask_perm_append))
  | false :: m', x :: xs ->
      let m' : vec (n-1) bool = m' in
      assert (filter_mask m' xs @ x :: filter_mask (mask_not m') xs
           == Perm.apply_perm_r (mask_perm_append #n (false :: m')) (x :: xs))
          by (tac_filter_mask_perm_append ();
              apply (`Perm.pequiv_trans_eq); later ();
                apply_raw (`Perm.pequiv_cons_eq); later (); later ();
                  apply_lemma (`filter_mask_perm_append);
                apply_raw (`Perm.pequiv_move_head_eq); later ();
              iterAll explode;
              iterAll (trefl <|> smt))

let filter_mask_perm_append' (#a : Type) (#n : nat) (m : vec n bool) (l : vec n a)
  : Lemma (l == Perm.apply_perm_r (mask_perm_append' m) (filter_mask m l @ filter_mask (mask_not m) l))
  =
    filter_mask_perm_append m l;
    mask_perm_append_inv m;
    Perm.apply_r_comp (mask_perm_append' m) (mask_perm_append m) l


let tac_filter_mask_or () : Tac unit =
  norm [delta_only [`%mask_or_append_f]; zeta];
  norm [iota];
  norm [delta_only [`%U.cast]; iota]

#push-options "--z3rlimit 60"
let rec filter_mask_or_append
      (#a : Type) (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len (mask_not m0)) bool) (l : vec len a)
  : Lemma (ensures filter_mask m0 l @ filter_mask m1 (filter_mask (mask_not m0) l)
                   == Perm.apply_perm_r (mask_or_append_f m0 m1) (filter_mask (mask_comp_or m0 m1) l))
        (decreases len)
  = match m0, m1, l with
  | [], [], [] -> ()
  | true :: m0', m1, x :: xs ->
      let m0' : vec (len-1) bool = m0'    in
      let lhs = filter_mask m0' xs @ filter_mask m1 (filter_mask (mask_not m0') xs) in
      let rhs = filter_mask (mask_comp_or m0' m1) xs in
      assert (x :: lhs == Perm.apply_perm_r (mask_or_append_f #len (true :: m0') m1) (x :: rhs))
          by (tac_filter_mask_or ();
              apply (`Perm.pequiv_cons_eq); smt ();
                apply_lemma (`filter_mask_or_append))
  | false :: m0', true :: m1', x :: xs ->
      let m0' : vec (len-1) bool = m0' in
      let lhs0 = filter_mask m0' xs in
      let lhs1 = filter_mask m1' (filter_mask (mask_not m0') xs) in
      let rhs  = filter_mask (mask_comp_or m0' m1') xs in
      assert (filter_mask m0 l @ filter_mask m1 (filter_mask (mask_not m0) l) == lhs0 @ x :: lhs1);
      assert (Perm.apply_perm_r (mask_or_append_f m0 m1) (filter_mask (mask_comp_or m0 m1) l)
           == Perm.apply_perm_r (mask_or_append_f #len (false :: m0') (true :: m1')) (x :: rhs));
      assert (lhs0 @ x :: lhs1 == Perm.apply_perm_r (mask_or_append_f #len (false :: m0') (true :: m1')) (x :: rhs))
          by (tac_filter_mask_or ();
              apply (`Perm.pequiv_trans_eq); later ();
                apply_raw (`Perm.pequiv_cons_eq); later (); later ();
                  apply_lemma (`filter_mask_or_append);
                apply_raw (`Perm.pequiv_move_head_eq); later ();
              explode (); trefl (); iterAll smt)
  | false :: m0, false :: m1, x :: xs ->
      let m0 : vec (len-1) bool = m0 in
      filter_mask_or_append m0 m1 xs
#pop-options

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

#push-options "--ifuel 1 --fuel 1"
let rec filter_mask_dl_append
      (#n0 #n1 : nat) (m0 : vec n0 bool) (m1 : vec n1 bool)
      (ts0 : vec n0 Type) (ts1 : vec n1 Type)
      (xs0 : Dl.dlist ts0) (xs1 : Dl.dlist ts1)
  : Lemma
    (ensures (filter_mask_append m0 m1 ts0 ts1;
        filter_mask_dl #(n0 + n1) (m0 @ m1) (ts0 @ ts1) (Dl.append xs0 xs1)
     == Dl.append (filter_mask_dl m0 ts0 xs0) (filter_mask_dl m1 ts1 xs1)))
    (decreases n0)
  = filter_mask_append m0 m1 ts0 ts1;
  match m0 with
  | [] -> let Dl.DNil = xs0 in ()
  | _ :: m0 -> let Dl.DCons _ _ ts0 xs0 = xs0 in
             filter_mask_dl_append #(n0-1) m0 m1 ts0 ts1 xs0 xs1
#pop-options

#push-options "--ifuel 0 --fuel 0"
let filter_mask_fl_perm_append (#n : nat) (m : vec n bool) (ts : vec n Type) (xs : Fl.flist ts)
  : Lemma (Fl.apply_pequiv (mask_pequiv_append m ts) xs
        == Fl.append (filter_mask_fl m ts xs) (filter_mask_fl (mask_not m) ts xs))
  = Fl.flist_extensionality
      (Fl.apply_pequiv (mask_pequiv_append m ts) xs)
      (Fl.append (filter_mask_fl m ts xs) (filter_mask_fl (mask_not m) ts xs))
      (fun i -> mask_perm_append_index m i)

let filter_mask_fl_and
      (#len : nat) (m0 : vec len bool) (m1 : vec (mask_len m0) bool) (ts : vec len Type)
      (xs : Fl.flist ts)
  : Lemma (filter_mask_and m0 m1 ts;
           filter_mask_fl (mask_comp_and m0 m1) ts xs == filter_mask_fl m1 _ (filter_mask_fl m0 ts xs))
  =
    filter_mask_and m0 m1 ts;
    Fl.flist_extensionality
      (filter_mask_fl (mask_comp_and m0 m1) ts xs)
      (filter_mask_fl m1 _ (filter_mask_fl m0 ts xs))
      (fun j -> ())

let filter_mask_fl_append
      (#n0 #n1 : nat) (m0 : vec n0 bool) (m1 : vec n1 bool)
      (ts0 : vec n0 Type) (ts1 : vec n1 Type)
      (xs0 : Fl.flist ts0) (xs1 : Fl.flist ts1)
  : Lemma (filter_mask_append m0 m1 ts0 ts1;
        filter_mask_fl #(n0 + n1) (m0 @ m1) (ts0 @ ts1) (Fl.append xs0 xs1)
     == Fl.append (filter_mask_fl m0 ts0 xs0) (filter_mask_fl m1 ts1 xs1))
  =
    let m : vec (n0+n1) bool = m0 @ m1 in
    let fd0 = filter_mask_dl m0 ts0 (Fl.dlist_of_f xs0) in
    let fd1 = filter_mask_dl m1 ts1 (Fl.dlist_of_f xs1) in
    filter_mask_append m0 m1 ts0 ts1;
    calc (==) {
      filter_mask_fl m (ts0 @ ts1) (Fl.append xs0 xs1);
    == { filter_mask_f_dl_f m _ (Fl.append xs0 xs1) }
      Fl.flist_of_d (filter_mask_dl m (ts0 @ ts1) (Fl.dlist_of_f (Fl.append xs0 xs1)));
    == { Fl.dlist_of_f_append xs0 xs1 }
      Fl.flist_of_d (filter_mask_dl m (ts0 @ ts1) (Dl.append (Fl.dlist_of_f xs0) (Fl.dlist_of_f xs1)));
    == { filter_mask_dl_append m0 m1 ts0 ts1 (Fl.dlist_of_f xs0) (Fl.dlist_of_f xs1) }
      Fl.flist_of_d (Dl.append fd0 fd1);
    == { Fl.dlist_of_f_append (Fl.flist_of_d fd0) (Fl.flist_of_d fd1) }
      Fl.append (Fl.flist_of_d fd0) (Fl.flist_of_d fd1);
    == { filter_mask_f_dl_f m0 ts0 xs0; filter_mask_f_dl_f m1 ts1 xs1 }
      Fl.append (filter_mask_fl m0 ts0 xs0) (filter_mask_fl m1 ts1 xs1);
    }

#pop-options
