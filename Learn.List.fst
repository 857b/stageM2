module Learn.List

open FStar.Calc
open FStar.Classical.Sugar
open FStar.List.Pure

module U = Learn.Util
module T  = FStar.Tactics
module Cl = FStar.Classical

let rec append_index (#a:Type) (l1 l2 : list a) (i : nat{i < length l1 + length l2}):
  Lemma (index (l1@l2) i == (if i < length l1 then index l1 i else index l2 (i - length l1)))
  = match l1 with
    | [] -> ()
    | _ :: tl -> if i = 0 then () else append_index tl l2 (i-1)

(* [reverse] *)
(* TODO: already defined as [rev'] *)
let rec reverse (#a:Type) (l : list a) : list a =
  match l with
  | [] -> []
  | hd :: tl -> (reverse tl)@[hd]

let rec reverse_length (#a:Type) (l : list a)
  : Lemma (length (reverse l) = length l) [SMTPat (length (reverse l))]
  = match l with
  | [] -> ()
  | hd :: tl -> reverse_length tl;
              append_length tl [hd]

let rec reverse_index (#a:Type) (l : list a) (i : nat{i < length l})
  : Lemma (index (reverse l) i == index l (length l - 1 - i))
  = match l with
  | [] -> ()
  | hd :: tl ->
       append_index (reverse tl) [hd] i;
       if i < length tl then reverse_index tl i
    
let rec rev_acc_reverse (#a : Type) (l1 l2 : list a) :
  Lemma (rev_acc l1 l2 == (reverse l1)@l2)
  = match l1 with
  | [] -> ()
  | hd :: tl -> rev_acc_reverse tl (hd :: l2);
              append_assoc (reverse tl) [hd] l2

let rev_reverse (#a : Type) (l : list a):
  Lemma (rev l == reverse l)
  = rev_acc_reverse l []

(* [for_allP] *)

let rec for_allP (#a : Type) (f : a -> prop) (l : list a) : prop
  = match l with
    | [] -> True
    | hd :: tl -> f hd /\ for_allP f tl

let rec for_allP_morph_strong (#a : Type) (f g : a -> prop) (l : list a) :
  Lemma (requires for_allP (fun x -> f x <==> g x) l)
        (ensures  for_allP f l <==> for_allP g l)
  = match l with
    | [] -> ()
    | _ :: tl -> for_allP_morph_strong f g tl

let rec for_allP_True (#a : Type) (f : a -> prop) (l : list a) :
  Lemma (requires forall x. f x) (ensures for_allP f l)
  = match l with
    | [] -> ()
    | _ :: tl -> for_allP_True f tl

let for_allP_morph (#a : Type) (f g : a -> prop) (l : list a) :
  Lemma (requires forall x . f x <==> g x)
        (ensures  for_allP f l <==> for_allP g l)
  = for_allP_True (fun x -> f x <==> g x) l;
    for_allP_morph_strong f g l

let rec for_allP_mem (#a : Type) (f : a -> prop) (l : list a)
  : Lemma (for_allP f l <==> (forall x . memP x l ==> f x))
  = match l with
    | [] -> ()
    | _ :: tl -> for_allP_mem f tl

let rec for_allP_index (#a : Type) (f : a -> prop) (l : list a)
  : Lemma (for_allP f l <==> (forall (i:nat{i < length l}) . f (index l i)))
  = match l with
    | [] -> ()
    | hd :: tl ->
      calc (<==>) {
        for_allP f l;
      <==> {for_allP_index f tl}
        f (index l 0) /\ (forall (i:nat{i < length tl}). f (index tl i));
      <==> {}
        f (index l 0) /\ (forall (i:nat{i < length tl}). f (index (hd :: tl) (i+1)));
      <==> {}
        f (index l 0) /\ (forall (i:nat{i < length tl}).{:pattern (f (index l (i+1)))}
                                                 f (index l (i+1)));
      <==> {}
        (forall (i:nat{i< length l}). if i=0 then f (index l 0) else f (index l (i-1+1)));
      }

let rec for_allP_append (#a : Type) (f : a -> prop) (l1 l2 : list a)
  : Lemma (for_allP f (l1@l2) <==> for_allP f l1 /\ for_allP f l2)
          [SMTPat (for_allP f (l1@l2))]
  = match l1 with
    | [] -> ()
    | _ :: tl -> for_allP_append f tl l2

let rec for_allP_reverse (#a : Type) (f : a -> prop) (l : list a)
  : Lemma (for_allP f (reverse l) <==> for_allP f l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      calc (<==>) {
        for_allP f (reverse l);
      <==> {}
        for_allP f (reverse tl) /\ for_allP f [hd];
      <==> {for_allP_reverse f tl}
        for_allP f tl /\ f hd;
      <==> {}
        for_allP f (hd :: tl);
      }

(* [for_all_opairsP] *)

let rec for_all_opairsP (#a : Type) (f : a -> a -> prop) (l : list a) : prop
  = match l with
    | [] -> True
    | hd :: tl -> for_allP (f hd) tl /\ for_all_opairsP f tl

(*
let iffI (d0 : T.term -> T.Tac unit) (d1 : T.term -> T.Tac unit) : T.Tac unit =
  T.(split (); iseq [(fun () -> let h = implies_intro () in d0 h);
                     (fun () -> let h = implies_intro () in d1 h)])

let test_iff (a : Type) (p : a -> Type) : GTot (squash ((forall x . p x) <==> (forall x . p x))) =
  _ by T.(iffI (fun h -> let x  = forall_intro () in
                      let h' = instantiate h x in
                      hyp h')
               (fun _ -> smt ()))

let test_impl (p : nat -> Type) (l : p 0 -> squash (p 1)) : GTot ((squash (p 0 ==> p 1))) =
  _ by T.(let h = implies_intro () in apply (quote l); hyp h)
*)

let rec for_all_opairsP_index (#a : Type) (f : a -> a -> prop) (l : list a)
  : Lemma (for_all_opairsP f l
           <==> (forall (i j : (x:nat{x < length l})). i < j ==> f (index l i) (index l j)))
  = match l with
    | [] -> ()
    | hd :: tl ->
         introduce
              (forall (j:nat{j < length tl}). f hd (index tl j))
           /\ (forall (i j : (x:nat{x < length tl})). i < j ==> f (index tl i) (index tl j))
           ==>
              (forall (i j : (x:nat{x < length l})). i < j ==> f (index l i) (index l j))
         with h. introduce forall (i j : (x:nat{x < length l})). i < j ==> f (index l i) (index l j)
         with introduce i < j ==> f (index l i) (index l j)
         with lt.
              if i = 0
              then eliminate forall (j':nat{j' < length tl}). f hd (index tl j')
                        with (j-1)
              else eliminate forall (i j : (x:nat{x < length tl})). i < j ==> f (index tl i) (index tl j)
                        with (i-1) (j-1)
         ;
         calc (<==>) {
           for_all_opairsP f (hd :: tl);
         <==> {}
           for_allP (f hd) tl /\ for_all_opairsP f tl;
         <==> {for_allP_index (f hd) tl; for_all_opairsP_index f tl}
              (forall (j:nat{j < length tl}). f hd (index tl j))
           /\ (forall (i j : (x:nat{x < length tl})). i < j ==> f (index tl i) (index tl j));
         <==> { }
              (forall (j:nat{j < length tl}). f (index l 0) (index l (j+1)))
           /\ (forall (i j : (x:nat{x < length tl})). i < j ==> f (index l (i+1)) (index l (j+1)));
         <==> {}
           forall (i j : (x:nat{x < length l})).{:pattern (f (index l i) (index l j))} i < j ==> f (index l i) (index l j);
         }

let rec for_all_opairsP_append (#a : Type) (f : a -> a -> prop) (l1 l2 : list a)
  : Lemma (for_all_opairsP f (l1@l2)
           <==> for_all_opairsP f l1 /\ for_all_opairsP f l2 /\ for_allP (fun x -> for_allP (f x) l2) l1)
  = match l1 with
    | [] -> ()
    | _ :: tl -> for_all_opairsP_append f tl l2

let flip (#a #b #c : Type) (f : a -> b -> c) : b -> a -> c = fun x y -> f y x

let for_all_opairsP_reverse (#a : Type) (f : a -> a -> prop) (l : list a)
  : Lemma (for_all_opairsP f (reverse l) <==> for_all_opairsP (flip f) l)
  =
  let flip_f = flip f in
  calc (<==>) {
      for_all_opairsP f (reverse l);
    <==> {for_all_opairsP_index f (reverse l)}
      forall (i j : (x:nat{x < length l})). i < j ==> f (index (reverse l) i) (index (reverse l) j);
    <==> {introduce forall (i:nat{i < length l}). index (reverse l) i == index l (length l - 1 - i)
             with reverse_index l i}
      forall (i j : (x:nat{x < length l})). i < j ==> f (index l (length l - 1 - i)) (index l (length l - 1 - j));
    <==> {
      introduce (forall (i j : (x:nat{x < length l})). i < j ==> f (index l (length l - 1 - i)) (index l (length l - 1 - j)))
                ==> (forall (i j : (x:nat{x < length l})). i < j ==> f (index l j) (index l i))
       with h. introduce forall (i j : (x:nat{x < length l})). i < j ==> f (index l j) (index l i)
       with eliminate forall (i j : (x:nat{x < length l})). i < j ==> f (index l (length l - 1 - i)) (index l (length l - 1 - j))
                 with (length l - 1 - j) (length l - 1 - i)
    }
      forall (i j : (x:nat{x < length l})). i < j ==> f (index l j) (index l i);
    <==> { assert_norm(forall x y. flip_f x y == f y x) }
      forall (i j : (x:nat{x < length l})). i < j ==> flip_f (index l i) (index l j);
    <==> { for_all_opairsP_index flip_f l }
      for_all_opairsP (flip f) l;
  }


(* [initi] *)

let rec initi (#a : Type) (lb ub : nat) (f : (i:nat{lb <= i /\ i < ub}) -> Tot a)
  : Tot (list a) (decreases ub - lb)
  = if lb < ub then f lb :: initi (lb + 1) ub f else []

(* [insert] *)

let rec insert (#a : Type) (i : nat) (x : a) (l : list a)
  : Pure (list a) (requires i <= length l) (ensures fun r -> length r = length l + 1)
         (decreases i)
  = if i = 0 then x :: l
    else let Cons hd tl = l in
         hd :: insert (i - 1) x tl

let rec insert_index (#a : Type) (i : nat) (x : a) (l : list a)
  : Lemma (requires i <= length l)
          (ensures index (insert i x l) i == x)
          (decreases i)
  = if i = 0 then ()
    else insert_index (i - 1) x (tail l)

let rec map_insert (#a #b : Type) (f : a -> b) (i : nat) (x : a) (l : list a)
  : Lemma (requires i <= length l)
          (ensures map f (insert i x l) == insert i (f x) (map f l))
          (decreases i)
  = if i = 0 then ()
    else map_insert f (i - 1) x (tail l)

(* [set] *)

let rec set (#a : Type) (i : nat) (x : a) (l : list a)
  : Pure (list a) (requires i < length l) (ensures fun r -> length r = length l)
         (decreases i)
  = let hd :: tl = l in
    if i = 0 then x :: tl
    else hd :: set (i - 1) x tl

(* [map_index] *)

let rec map_index (#a : Type) (i : nat) (f : a -> a) (l : list a)
  : Pure (list a) (requires i < length l) (ensures fun r -> length r = length l)
         (decreases i)
  = let hd :: tl = l in
    if i = 0 then f hd :: tl
    else hd :: map_index (i - 1) f tl

let rec set_is_map_index (#a : Type) (i : nat) (x : a) (l : list a)
  : Lemma (requires  i < length l)
          (ensures   set i x l == map_index i (fun _ -> x) l)
          (decreases i)
  = if i = 0 then () else set_is_map_index (i-1) x (tail l)

(* [splitAt] *)

let rec lemma_splitAt_append (#a:Type) (n:nat) (l:list a) :
  Lemma (ensures (let l1, l2 = splitAt n l in append l1 l2 == l)) =
  match n with
  | 0 -> ()
  | _ ->
    match l with
    | [] -> ()
    | x :: xs -> lemma_splitAt_append (n-1) xs

(* [permutation] *)

noeq type permutation_t (#a : Type) : list a -> list a -> Type =
  | Perm_swap : l0 : list a -> x : a -> y : a -> l1 : list a ->
              permutation_t (l0 @ x :: y :: l1) (l0 @ y :: x :: l1)
  | Perm_refl  : l : list a -> permutation_t l l
  | Perm_trans : l0 : list a -> l1 : list a -> l2 : list a ->
              permutation_t l0 l1 -> permutation_t l1 l2 ->
              permutation_t l0 l2

type permutation #a l0 l1 = squash (permutation_t #a l0 l1)

module Mnd = FStar.Algebra.Monoid

let append_monoid (a : Type) : Mnd.monoid (list a) =
  U.assert_by (Mnd.right_unitality_lemma (list a) [] (append #a) /\ True)
    (fun () -> assert (forall (l : list a) . l @ [] == l));
  assert (Mnd.left_unitality_lemma (list a) [] (append #a));
  U.assert_by (Mnd.associativity_lemma (list a) (append #a) /\ True)
    (fun () -> assert (Mnd.associativity_lemma (list a) (append #a) ==
                       (forall (x y z : list a) . (x @ y) @ z == x @ (y @ z)))
                by T.(norm [delta]; trefl ());
            introduce forall (x y z : list a) . x @ (y @ z) == (x @ y) @ z
                 with append_assoc x y z);
  Mnd.intro_monoid (list a) [] (append #a)


let rec permutation_t_sym #a l0 l1 (p : permutation_t #a l0 l1)
  : Tot (permutation_t #a l1 l0)
        (decreases p)
  = match p with
    | Perm_refl l -> Perm_refl l
    | Perm_swap l0 x y l1 -> Perm_swap l0 y x l1
    | Perm_trans l0 l1 l2 p0 p1 -> Perm_trans l2 l1 l0 (permutation_t_sym _ _ p1) (permutation_t_sym _ _ p0)

let rec permutation_t_append (#a : Type) (pre l0 l1 sfx : list a) (p : permutation_t l0 l1)
  : Tot (permutation_t (pre @ l0 @ sfx) (pre @ l1 @ sfx))
        (decreases p)
  = match p with
    | Perm_swap l0 x y l1 ->
                introduce forall x y . (pre @ l0) @ x :: y :: (l1 @ sfx) == pre @ (l0 @ x :: y :: l1) @ sfx
                  with calc ( == ) {
                    (pre @ l0) @ x :: y :: (l1 @ sfx);
                  == {append_assoc pre l0 (x :: y :: (l1 @ sfx))}
                    pre @ (l0 @ [x; y] @ (l1 @ sfx));
                  == {append_assoc l0 [x; y] (l1 @ sfx)}
                    pre @ ((l0 @ [x; y]) @ (l1 @ sfx));
                  == {append_assoc (l0@[x; y]) l1 sfx}
                    pre @ (((l0 @ [x; y]) @ l1) @ sfx);
                  == {append_assoc l0 [x; y] l1}
                    pre @ (l0 @ x :: y :: l1) @ sfx;
                  };
                Perm_swap (pre @ l0) x y (l1 @ sfx)
    | Perm_refl l0 -> Perm_refl _
    | Perm_trans l0 l1 l2 p0 p1 ->
                 Perm_trans _ _ _ (permutation_t_append pre l0 l1 sfx p0)
                                  (permutation_t_append pre l1 l2 sfx p1)

let rec permutation_t_cons_snoc #a x l
  : Tot (permutation_t #a (x :: l) (snoc (l,x)))
        (decreases l)
  = match l with
    | [] -> Perm_refl _
    | hd :: tl ->
      Perm_trans _ _ _ (Perm_swap [] x hd tl)
                       (permutation_t_append [hd] (x :: tl) (snoc (tl,x)) []
                         (permutation_t_cons_snoc #a x tl))
        
let rec permutation_t_reverse #a l
  : Tot (permutation_t #a l (reverse l))
        (decreases l)
  = match l with
    | [] -> Perm_refl _
    | hd :: tl ->
      Perm_trans _ _ _ (permutation_t_cons_snoc hd tl)
                       (permutation_t_append [] tl (reverse tl) [hd]
                         (permutation_t_reverse tl))

(* [g_fold_right] *)

let rec fold_right_gtot_append #a #b l0 l1 f x
  : Lemma (ensures fold_right_gtot #a #b (l0@l1) f x == fold_right_gtot l0 f (fold_right_gtot l1 f x))
          (decreases l0)
  = match l0 with
    | [] -> ()
    | hd :: tl -> fold_right_gtot_append tl l1 f x

let fold_right_gtot_f_comm #a #b (f : a -> b -> GTot b) : prop =
  forall (x0 x1 : a) (y : b) . f x0 (f x1 y) == f x1 (f x0 y)

let rec fold_right_gtot_comm_permutation_t #a #b l0 l1 f x (p : permutation_t l0 l1)
  : Lemma (requires fold_right_gtot_f_comm #a #b f)
          (ensures fold_right_gtot l0 f x == fold_right_gtot l1 f x)
          (decreases p)
  = match p with
    | Perm_refl _ -> ()
    | Perm_swap l0 x0 x1 l1 ->
                fold_right_gtot_append l0 (x0 :: x1 :: l1) f x;
                fold_right_gtot_append l0 (x1 :: x0 :: l1) f x
    | Perm_trans l0 l1 l2 p0 p1 ->
                fold_right_gtot_comm_permutation_t l0 l1 f x p0;
                fold_right_gtot_comm_permutation_t l1 l2 f x p1
