module Learn.List

open FStar.Calc
open FStar.Classical.Sugar
open FStar.List.Pure

module T  = FStar.Tactics
module Cl = FStar.Classical

let rec append_index (#a:Type) (l1 l2 : list a) (i : nat{i < length l1 + length l2}):
  Lemma (index (l1@l2) i == (if i < length l1 then index l1 i else index l2 (i - length l1)))
  = match l1 with
    | [] -> ()
    | _ :: tl -> if i = 0 then () else append_index tl l2 (i-1)

(* [reverse] *)

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

let iff (a b : Type) : Type = (a -> b) & (b -> a)

let rec for_all_opairsP_index (#a : Type) (f : a -> a -> prop) (l : list a)
  : Lemma (for_all_opairsP f l
           <==> (forall (i j : (x:nat{x < length l})). i < j ==> f (index l i) (index l j)))
  = match l with
    | [] -> ()
    | hd :: tl ->
         (*let lem0 :
           ((j:nat{j < length tl} -> f hd (index tl j))
             & ((i:nat{i < length tl}) -> j:nat{j < length tl} -> squash (i < j) -> f (index tl i) (index tl j)))
           ->
           (i:nat{i < length l} -> j:nat{j < length l} -> squash (i < j) -> f (index l i) (index l j))
           = fun (h0, h1) i j lt -> if i = 0 then h0 (j-1) else h1 (i-1) (j-1) ()
         in*)
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
       (* let lem1 :
           (i:nat{i < length l} -> j:nat{j < length l} -> squash (i < j) -> f (index l i) (index l j))
           ->
           ((j:nat{j < length tl} -> f hd (index tl j))
             & ((i:nat{i < length tl}) -> j:nat{j < length tl} -> squash (i < j) -> f (index tl i) (index tl j)))
           = fun h -> (fun (j:nat{j<length tl}) -> h 0 (j+1) ()),
                   (fun (i:nat{i<length tl}) (j:nat{j<length tl}) lt -> h (i+1) (j+1) ())
         in*)
       (*
         introduce
              (forall (i j : (x:nat{x < length l})). i < j ==> f (index l i) (index l j))
           ==>
              (forall (j:nat{j < length tl}). f hd (index tl j))
           /\ (forall (i j : (x:nat{x < length tl})). i < j ==> f (index tl i) (index tl j))
         with h. introduce (forall (j:nat{j < length tl}). f hd (index tl j))
                        /\ (forall (i j : (x:nat{x < length tl})). i < j ==> f (index tl i) (index tl j))
           with (introduce forall (j:nat{j < length tl}). _
                 with eliminate forall i j. i < j ==> f (index l i) (index l j)
                           with 0 (j+1))
            and (introduce forall (i j : (x:nat{x < length tl})). _
                 with eliminate forall i j. i < j ==> f (index l i) (index l j)
                           with (i+1) (j+1));*)

         calc (<==>) {
           for_all_opairsP f (hd :: tl);
         <==> {}
           for_allP (f hd) tl /\ for_all_opairsP f tl;
         <==> {for_allP_index (f hd) tl; for_all_opairsP_index f tl}
              (forall (j:nat{j < length tl}). f hd (index tl j))
           /\ (forall (i j : (x:nat{x < length tl})). i < j ==> f (index tl i) (index tl j));
         <==> {}
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
