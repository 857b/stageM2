module Learn.DList

module U    = Learn.Util
module L    = FStar.List.Pure
module Ll   = Learn.List
module Perm = Learn.Permutation

(*** Dependent lists *)

type ty_list = list Type

noeq
type dlist : ty_list -> Type =
  | DNil : dlist []
  | DCons : (t0 : Type) -> (x0 : t0) ->
             (ts : ty_list) -> (xs : dlist ts) ->
             dlist (t0 :: ts)


let rec index (#ts : ty_list) (xs : dlist ts) (i : nat{i < L.length ts})
  : L.index ts i
  = let DCons t0 x0 ts1 xs1 = xs in
    if i = 0 then x0
    else U.cast (L.index ts i) (index xs1 (i-1))

let rec dlist_extensionality (#ts : ty_list) (xs ys : dlist ts)
  : Lemma (requires forall (i : nat {i < L.length ts}) . index xs i == index ys i)
          (ensures xs == ys)
          (decreases ts)
  = match ts with
    | [] -> ()
    | t0 :: ts' -> let DCons _ x _ xs' = xs in
                let DCons _ y _ ys' = ys in
                assert (x == index xs 0);
                assert (y == index ys 0);
                introduce forall (i : nat {i < L.length ts'}) . index xs' i == index ys' i
                  with (assert (index xs' i === index xs (i+1));
                        assert (index ys' i === index ys (i+1)));
                dlist_extensionality #ts' xs' ys'


let rec splitAt (n : nat) (#ts : ty_list) (xs : dlist ts)
  : Tot (dlist (L.splitAt n ts)._1 & dlist (L.splitAt n ts)._2)
        (decreases n)
  = if n = 0 then DNil, xs
    else match xs with
    | DNil              -> DNil, DNil
    | DCons t0 x0 ts xs -> let xs0, xs1 = splitAt (n-1) xs in
                           DCons t0 x0 _ xs0, xs1

let rec splitAt_ty (ts0 ts1 : ty_list) (xs : dlist L.(ts0@ts1))
  : Tot (dlist ts0 & dlist ts1) (decreases ts0)
  = match ts0 with
    | [] -> DNil, xs
    | t0 :: ts0 -> let DCons _ x0 _ xs = xs in
                 let xs0, xs1 = splitAt_ty ts0 ts1 xs in
                 DCons t0 x0 _ xs0, xs1

let rec splitAt_ty_eq (ts0 ts1 : ty_list) (xs : dlist L.(ts0@ts1))
  : Lemma (ensures L.(splitAt (length ts0) (ts0@ts1) == (ts0, ts1)) /\
                   splitAt_ty ts0 ts1 xs == splitAt L.(length ts0) xs)
          (decreases ts0)
  = match ts0 with
  | [] -> ()
  | t0 :: ts0 -> let DCons _ x0 _ xs = xs in splitAt_ty_eq ts0 ts1 xs


let rec initi (lb ub : nat)
          (t : (i:nat{lb <= i /\ i < ub}) -> Tot Type)
          (f : (i:nat{lb <= i /\ i < ub}) -> Tot (t i))
  : Tot (dlist (Ll.initi lb ub t)) (decreases ub - lb)
  = if lb < ub then DCons (t lb) (f lb) _ (initi (lb + 1) ub t f) else DNil

let rec initi_at (lb ub : nat)
          (t : (i:nat{lb <= i /\ i < ub}) -> Tot Type)
          (f : (i:nat{lb <= i /\ i < ub}) -> Tot (t i))
          (i : nat {i < L.length (Ll.initi lb ub t)})
  : Lemma (ensures index (initi lb ub t f) i == f (lb+i)) (decreases i)
          [SMTPat (index (initi lb ub t f) i)]
  = if i = 0 then () else initi_at (lb+1) ub t f (i-1)


(** permutations *)

let apply_perm_r (#n : nat) (p : Perm.perm_f n) (#ts : ty_list {L.length ts == n}) (xs : dlist ts)
  : dlist (Perm.apply_perm_r p ts)
  = initi 0 n (fun i -> L.index ts (p i)) (fun i -> index xs (p i))

let apply_r_id_n (len : nat) (#ts : ty_list{L.length ts = len}) (xs :dlist ts)
  : Lemma (apply_perm_r (Perm.id_n len) xs == xs) [SMTPat (apply_perm_r (Perm.id_n len) xs)]
  = dlist_extensionality (apply_perm_r (Perm.id_n len) xs) xs

let apply_r_comp (#len : nat) (f g : Perm.perm_f len) (#ts : ty_list {L.length ts == len}) (xs : dlist ts)
  : Lemma (apply_perm_r (f `Perm.comp` g) xs === apply_perm_r f (apply_perm_r g xs))
  = Perm.apply_r_comp f g ts;
    dlist_extensionality (apply_perm_r (f `Perm.comp` g) xs) (apply_perm_r f (apply_perm_r g xs))

let rec dlist_swap (i : nat) (#ts : ty_list{i <= L.length ts - 2}) (xs : dlist ts)
  : Tot (dlist (Perm.list_swap i ts)) (decreases i)
  = if i = 0
    then let DCons tx x _ (DCons ty y _ tl) = xs in
         DCons ty y _ (DCons tx x _ tl)
    else let DCons tx x ts tl = xs in
         DCons tx x _ (dlist_swap (i-1) tl)

#push-options "--z3rlimit 20"
let apply_perm_f_shift (#len : nat) (p : Perm.perm_f len)
      (#hd_ty : Type) (#tl_ty : ty_list {L.length tl_ty = len})
      (hd : hd_ty) (tl : dlist tl_ty)
  : Lemma (apply_perm_r (Perm.perm_f_shift p) (DCons _ hd _ tl)
       === DCons _ hd _ (apply_perm_r p tl))
  = Perm.apply_perm_f_shift p hd_ty tl_ty;
    dlist_extensionality
      (apply_perm_r (Perm.perm_f_shift p) (DCons _ hd _ tl))
      (DCons _ hd _ (apply_perm_r p tl))
#pop-options

#push-options "--z3rlimit 60"
let rec apply_swap_as_rec (len : nat) (i : nat {i <= len-2})
          (#ts : ty_list {L.length ts = len}) (xs : dlist ts)
  : Lemma (ensures apply_perm_r (Perm.perm_f_swap #len i) xs === dlist_swap i xs)
          (decreases len)
  = Perm.apply_swap_as_rec len i ts;
    if i = 0 then begin
       let DCons _ x _ (DCons _ y _ tl) = xs in
       dlist_extensionality
         (apply_perm_r (Perm.perm_f_swap #len 0) (DCons _ x _ (DCons _ y _ tl)))
         (DCons _ y _ (DCons _ x _ tl))
    end else begin
      let DCons _ hd _ tl = xs in
      Perm.perm_f_swap_rec_rel (len-1) (i-1);
      apply_perm_f_shift (Perm.perm_f_swap #(len-1) (i-1)) hd tl;
      apply_swap_as_rec (len-1) (i-1) tl
    end
#pop-options


unfold
let apply_pequiv (#ts0 #ts1 : ty_list) (f : Perm.pequiv ts0 ts1) (xs : dlist ts0) : dlist ts1
  = apply_perm_r f xs

let apply_pequiv_sym_l (#ts0 #ts1 : ty_list) (f : Perm.pequiv ts0 ts1) (xs : dlist ts0)
  : Lemma (apply_pequiv (Perm.pequiv_sym f) (apply_pequiv f xs) == xs)
  =
    apply_r_comp (Perm.inv_f f) f xs

let apply_pequiv_sym_r (#ts0 #ts1 : ty_list) (f : Perm.pequiv ts0 ts1) (xs : dlist ts1)
  : Lemma (apply_pequiv f (apply_pequiv (Perm.pequiv_sym f) xs) == xs)
  =
    Perm.pequiv_as_eq (Perm.pequiv_sym f);
    apply_r_comp f (Perm.inv_f f) xs


let apply_pequiv_sym_eq_iff (#ts0 #ts1 : ty_list) (f : Perm.pequiv ts0 ts1) (xs : dlist ts0) (ys : dlist ts1)
  : Lemma (xs == apply_pequiv (Perm.pequiv_sym f) ys <==> ys == apply_pequiv f xs)
  =
    apply_pequiv_sym_l f xs;
    apply_pequiv_sym_r f ys
