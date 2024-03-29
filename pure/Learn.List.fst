module Learn.List

open FStar.Calc
open FStar.Classical.Sugar
open FStar.List.Pure

module U   = Learn.Util
module T   = FStar.Tactics
module Tuq = Learn.Tactics.Unsquash
module Fin = FStar.Fin


type vec (n : nat) (a : Type) = llist a n
type dom (#a : Type) (l : list a) = Fin.fin (length l)

let list_extensionality (#a : Type)
      (l0 : list a) (l1 : list a {length l1 = length l0})
      (pf : (i : nat {i < length l0}) -> squash (index l0 i == index l1 i))
  : Lemma (l0 == l1)
  =
    introduce forall (i : nat {i < length l0}) . index l0 i == index l1 i
      with pf i;
    index_extensionality l0 l1

let list_extensionality_sq (#a : Type)
      (#l0 : list a) (#l1 : list a {length l1 = length l0})
      (pf : (i : nat {i < length l0}) -> squash (index l0 i == index l1 i))
  : squash (l0 == l1)
  = list_extensionality l0 l1 pf


let rec list_eq (#a : Type) (eq_a : U.eq_dec a) (l0 l1 : list a)
  : Tot (b : bool {b <==> l0 == l1}) (decreases l0)
  = match l0, l1 with
  | [], [] -> true
  | x :: xs, y :: ys -> x `eq_a` y && xs `list_eq eq_a` ys
  | _ -> false

(* [last], [init], [unsnoc] *)

#push-options "--ifuel 2 --fuel 2"
let rec last_index (#a : Type) (l : list a)
  : Lemma (requires Cons? l) (ensures last l == index l (length l - 1)) (decreases l)
  = match l with
  | [x] -> ()
  | x :: xs -> last_index xs
#pop-options

let rec init_length (#a : Type) (l : list a {Cons? l})
  : Lemma (ensures length (init l) == length l - 1) (decreases l)
          [SMTPat (length (init l))]
  = match l with
  | [_] -> ()
  | _ :: tl -> init_length tl

let rec unsnoc_eq_init (#a : Type) (l : list a {Cons? l})
  : Lemma (ensures unsnoc l == (init l, last l)) (decreases l)
  = match l with
  | [_] -> ()
  | _ :: tl -> unsnoc_eq_init tl

(* [memP] *)

#push-options "--ifuel 1 --fuel 1"
let rec memP_iff (#a : Type) (x : a) (l : list a)
  : Lemma (ensures memP x l <==> (exists (i : dom l) . index l i == x))
          (decreases l)
  = match l with
  | [] -> ()
  | y :: ys ->
      calc (<==>) {
        memP x l;
      <==> { }
        y == x \/ memP x ys;
      <==> { memP_iff x ys }
        index l 0 == x \/ (exists (i : dom ys) . index ys i == x);
      <==> { }
        index l 0 == x \/ (exists (i : Fin.fin (length l - 1)) . index l (i+1) == x);
      <==> { introduce forall (i : dom l) . i == 0 \/ (exists (i' : Fin.fin (length l - 1)) . i = i'+1)
             with if i > 0 then assert (i = (i-1)+1) }
        exists (i : dom l) . index l i == x;
      }
#pop-options

let rec append_memP (#a : Type) (x : a) (l0 l1 : list a)
  : Lemma (ensures memP x (l0 @ l1) <==> (memP x l0 \/ memP x l1))
  = match l0 with
  | [] -> ()
  | y :: l0 -> append_memP x l0 l1

(* [mem_findi] *)

let rec mem_findi (#a : eqtype) (x : a) (l : list a)
  : Pure (dom l)
         (requires mem x l)
         (ensures fun i -> index l i = x)
         (decreases l)
  = let hd :: tl = l in
    if x = hd then 0
    else 1 + mem_findi x tl


(* [map] *)

let rec map_index (#a #b : Type) (f : a -> b) (l : list a) (i : nat {i < length l})
  : Lemma (ensures index (map f l) i == f (index l i)) (decreases i)
          [SMTPat (index (map f l) i)]
  = let x :: xs = l in
    if i = 0 then () else map_index f xs (i-1)

let rec map_map (#a #b #c : Type) (f : b -> c) (g : a -> b) (h : a -> c) (l : list a)
  : Lemma (requires forall (x : a) . h x == f (g x))
          (ensures map f (map g l) == map h l)
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: tl -> map_map f g h tl

let rec map_append #a #b (f : a -> b) l0 l1
  : Lemma (ensures map f (l0@l1) == map f l0 @ map f l1)
          (decreases l0)
  = match l0 with
    | [] -> ()
    | _ :: tl -> map_append f tl l1

/// Those lemmas are equivalent to the ones of the standard library but use a
/// requires clause instead of an implication.
let memP_map_intro (#a #b: Type) (f: a -> Tot b) (x: a) (l: list a)
  : Lemma (requires memP x l) (ensures memP (f x) (map f l))
  = FStar.List.memP_map_intro f x l

let memP_map_elim (#a #b: Type) (f: a -> Tot b) (y: b) (l: list a)
  : Lemma (requires memP y (map f l)) (ensures (exists (x : a) . memP x l /\ f x == y))
  = FStar.List.memP_map_elim f y l

(* [map2] *)

let rec map2_length (#a1 #a2 #b: Type) (f: a1 -> a2 -> b) (l1:list a1) (l2:list a2)
  : Lemma (requires length l1 == length l2) (ensures length (map2 f l1 l2) == length l1)
          (decreases l1)
          [SMTPat (length (map2 f l1 l2))]
  = match l1, l2 with
  | [], [] -> ()
  | x :: xs, y :: ys -> map2_length f xs ys

let rec map2_index (#a1 #a2 #b: Type) (f: a1 -> a2 -> b) (l1:list a1) (l2:list a2) (i : dom l1)
  : Lemma (requires length l1 == length l2)
          (ensures index (map2 f l1 l2) i == f (index l1 i) (index l2 i))
          (decreases i)
          [SMTPat (index (map2 f l1 l2) i)]
  = if i > 0 then map2_index f (tl l1) (tl l2) (i-1)

(* [append] *)

let rec append_index (#a:Type) (l1 l2 : list a) (i : nat{i < length l1 + length l2}):
  Lemma (index (l1@l2) i == (if i < length l1 then index l1 i else index l2 (i - length l1)))
  = match l1 with
    | [] -> ()
    | _ :: tl -> if i = 0 then () else append_index tl l2 (i-1)

let pat_append ()
  : squash ((forall (a : Type) (l1 l2 : list a) (i : Fin.fin (length l1 + length l2)) .
             {:pattern (index (l1@l2) i)}
             index (l1@l2) i == (if i < length l1 then index l1 i else index l2 (i - length l1))) /\
           (forall (a b : Type) (f : a -> b) (l1 l2 : list a) .
             map f (l1@l2) == map f l1 @ map f l2))
  = introduce forall (a : Type) (l1 l2 : list a) (i : Fin.fin (length l1 + length l2)) .
              index (l1@l2) i == (if i < length l1 then index l1 i else index l2 (i - length l1))
      with append_index l1 l2 i;
    introduce forall (a b : Type) (f : a -> b) (l1 l2 : list a) .
              map f (l1@l2) == map f l1 @ map f l2
      with map_append f l1 l2


(* [filteri] *)

let rec filteri_aux (#a : Type) (#len : nat) (f : Fin.fin len -> a -> bool)
                    (i : nat{i <= len}) (l : llist a (len - i))
  : Tot (list a) (decreases l)
  = match l with
  | [] -> []
  | x :: xs -> if f i x then x :: filteri_aux f (i + 1) xs
             else filteri_aux f (i + 1) xs

let filteri (#a : Type) (#len : nat) (f : Fin.fin len -> a -> bool) (l : llist a len)
  : list a
  = filteri_aux f 0 l


(* [rev'] *)

let rec rev'_length (#a:Type) (l : list a)
  : Lemma (length (rev' l) = length l) [SMTPat (length (rev' l))]
  = match l with
  | [] -> ()
  | hd :: tl -> rev'_length tl;
              append_length tl [hd]

let rec rev'_index (#a:Type) (l : list a) (i : nat{i < length l})
  : Lemma (index (rev' l) i == index l (length l - 1 - i))
  = match l with
  | [] -> ()
  | hd :: tl ->
       append_index (rev' tl) [hd] i;
       if i < length tl then rev'_index tl i

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
        f hd /\ (forall (i:nat{i < length tl}). f (index tl i));
      <==> {_ by (Tuq.(lbd_prfs (`(_ /\ (forall i._) <==> (forall i._))))
               [(`(fun h_hd h_tl i -> if i = 0 then h_hd else h_tl (i-1)));
                (`(fun hi -> hi 0));
                (`(fun hi i -> hi (i+1)))])}
        (forall (i:nat{i< length (hd :: tl)}). f (index (hd :: tl) i));
      }

let rec for_allP_append (#a : Type) (f : a -> prop) (l1 l2 : list a)
  : Lemma (for_allP f (l1@l2) <==> for_allP f l1 /\ for_allP f l2)
          [SMTPat (for_allP f (l1@l2))]
  = match l1 with
    | [] -> ()
    | _ :: tl -> for_allP_append f tl l2

let rec for_allP_rev' (#a : Type) (f : a -> prop) (l : list a)
  : Lemma (for_allP f (rev' l) <==> for_allP f l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      calc (<==>) {
        for_allP f (rev' l);
      <==> {}
        for_allP f (rev' tl) /\ for_allP f [hd];
      <==> {for_allP_rev' f tl}
        for_allP f tl /\ f hd;
      <==> {}
        for_allP f (hd :: tl);
      }

(* [for_all_opairsP] *)

let rec for_all_opairsP (#a : Type) (f : a -> a -> prop) (l : list a) : prop
  = match l with
    | [] -> True
    | hd :: tl -> for_allP (f hd) tl /\ for_all_opairsP f tl

let rec for_all_opairsP_index (#a : Type) (f : a -> a -> prop) (l : list a)
  : Lemma (for_all_opairsP f l
           <==> (forall (i j : (x:nat{x < length l})). i < j ==> f (index l i) (index l j)))
  = match l with
    | [] -> ()
    | hd :: tl ->
         calc (<==>) {
           for_all_opairsP f (hd :: tl);
         <==> {}
           for_allP (f hd) tl /\ for_all_opairsP f tl;
         <==> {for_allP_index (f hd) tl; for_all_opairsP_index f tl}
              (forall (j:nat{j < length tl}). f hd (index tl j))
           /\ (forall (i j : (x:nat{x < length tl})). i < j ==> f (index tl i) (index tl j));
         <==> { _ by (Tuq.(lbd_prfs (`((forall j._) /\ (forall i j. _ ==> _) <==> (forall i j. _ ==> _))))
                        [(`(fun h_hd h_tl i j _ -> if i = 0 then h_hd (j-1) else h_tl (i-1) (j-1) ()));
                         (`(fun h j -> h 0 (j+1) ()));
                         (`(fun h i j _ -> h (i+1) (j+1) ()))])}
           forall (i j : (x:nat{x < length (hd :: tl)})). i < j ==> f (index (hd :: tl) i) (index (hd :: tl) j);
         }

let rec for_all_opairsP_append (#a : Type) (f : a -> a -> prop) (l1 l2 : list a)
  : Lemma (for_all_opairsP f (l1@l2)
           <==> for_all_opairsP f l1 /\ for_all_opairsP f l2 /\ for_allP (fun x -> for_allP (f x) l2) l1)
  = match l1 with
    | [] -> ()
    | _ :: tl -> for_all_opairsP_append f tl l2

let flip (#a #b #c : Type) (f : a -> b -> c) : b -> a -> c = fun x y -> f y x

let for_all_opairsP_rev' (#a : Type) (f : a -> a -> prop) (l : list a)
  : Lemma (for_all_opairsP f (rev' l) <==> for_all_opairsP (flip f) l)
  =
  let flip_f = flip f in
  calc (<==>) {
      for_all_opairsP f (rev' l);
    <==> {for_all_opairsP_index f (rev' l)}
      forall (i j : (x:nat{x < length l})). i < j ==> f (index (rev' l) i) (index (rev' l) j);
    <==> {introduce forall (i:nat{i < length l}). index (rev' l) i == index l (length l - 1 - i)
             with rev'_index l i}
      forall (i j : (x:nat{x < length l})). i < j ==> f (index l (length l - 1 - i)) (index l (length l - 1 - j));
    <==> {_ by (Tuq.(lbd_prfs (`((forall i j. _ ==> _) <==> (forall i j. _ ==> _))))
             [(`(fun h i j _ -> h (length (`@l) - 1 - j) (length (`@l) - 1 - i) ()));
              (`(fun h i j _ -> h (length (`@l) - 1 - j) (length (`@l) - 1 - i) ()))])}
      forall (i j : (x:nat{x < length l})). i < j ==> f (index l j) (index l i);
    <==> { assert_norm(forall x y. flip_f x y == f y x) }
      forall (i j : (x:nat{x < length l})). i < j ==> flip_f (index l i) (index l j);
    <==> { for_all_opairsP_index flip_f l }
      for_all_opairsP (flip f) l;
  }


(* [initi] *)

let rec initi (#a : Type) (lb ub : int) (f : (i:int{lb <= i /\ i < ub}) -> Tot a)
  : Tot (list a) (decreases ub - lb)
  = if lb < ub then f lb :: initi (lb + 1) ub f else []

let rec initi_length (#a : Type) (lb ub : int) (f : (i:int{lb <= i /\ i < ub}) -> Tot a)
  : Lemma (ensures length (initi lb ub f) = (if ub >= lb then ub - lb else 0)) (decreases ub - lb)
          [SMTPat (length (initi lb ub f))]
  = if lb < ub then initi_length (lb + 1) ub f else ()

let rec initi_index (#a : Type) (lb ub : int) (f : (i:int{lb <= i /\ i < ub}) -> Tot a)
                    (i : nat{i < length (initi lb ub f)})
  : Lemma (ensures index (initi lb ub f) i == f (lb+i)) (decreases i)
          [SMTPat (index (initi lb ub f) i)]
  = if i = 0 then ()
    else initi_index (lb+1) ub f (i-1)

(* [repeat] *)

let rec repeat (#a : Type) (n : nat) (x : a)
  : Tot (llist a n)
  = if n = 0 then [] else x :: repeat (n-1) x

let rec repeat_index (#a : Type) (n : nat) (x : a) (i : Fin.fin n)
  : Lemma (ensures index (repeat n x) i == x) (decreases n)
          [SMTPat (index (repeat n x) i)]
  = if i > 0 then repeat_index (n-1) x (i-1)

let rec repeat_count (#a : eqtype) (n : nat) (x x' : a)
  : Lemma (ensures count x' (repeat n x) == (if x = x' then n else 0)) (decreases n)
  = if n > 0 then repeat_count (n-1) x x'

let map_repeat (#a #b : Type) (f : a -> b) (n : nat) (x : a)
  : Lemma (map f (repeat n x) == repeat n (f x))
          [SMTPat (map f (repeat n x))]
  = list_extensionality (map f (repeat n x)) (repeat n (f x)) (fun i -> ())

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

let rec set_index (#a : Type) (i : nat) (x : a) (l : list a) (j : nat)
  : Lemma (requires i < length l /\ j < length l)
          (ensures  index (set i x l) j == (if j = i then x else index l j))
          (decreases j)
          [SMTPat (index (set i x l) j)]
  = if i = 0 || j = 0 then () else set_index (i-1) x (tl l) (j-1)


(* [map_nth] *)

let rec map_nth (#a : Type) (i : nat) (f : a -> a) (l : list a)
  : Pure (list a) (requires i < length l) (ensures fun r -> length r = length l)
         (decreases i)
  = let hd :: tl = l in
    if i = 0 then f hd :: tl
    else hd :: map_nth (i - 1) f tl

let rec map_nth_index (#a : Type) (i : nat) (f : a -> a) (l : list a) (j : dom l)
  : Lemma (requires  i < length l)
          (ensures   index (map_nth i f l) j == (if j = i then f (index l i) else index l j))
          (decreases j)
          [SMTPat (index (map_nth i f l) j)]
  = let hd :: tl = l in
    if j > 0 && i > 0 then map_nth_index (i-1) f tl (j-1)

let rec set_is_map_nth (#a : Type) (i : nat) (x : a) (l : list a)
  : Lemma (requires  i < length l)
          (ensures   set i x l == map_nth i (fun _ -> x) l)
          (decreases i)
  = if i = 0 then () else set_is_map_nth (i-1) x (tail l)


(* [splitAt] *)

/// same conclusion as [FStar.List.Pure.Properties.lemma_splitAt_append] but without the requirement on [n]
let rec lemma_splitAt_append (#a:Type) (n:nat) (l:list a) :
  Lemma (ensures (let l1, l2 = splitAt n l in append l1 l2 == l)) =
  match n with
  | 0 -> ()
  | _ ->
    match l with
    | [] -> ()
    | x :: xs -> lemma_splitAt_append (n-1) xs

let splitAt_index (#a : Type) (n : nat) (l : list a)
  : Lemma (requires n <= length l)
          (ensures (let l0, l1 = splitAt n l in
                    length l0 == n /\ length l1 == length l - n /\
                   (forall (i : dom l0) . {:pattern (index l0 i)}
                      index l0 i == index l i) /\
                   (forall (i : dom l1) . {:pattern (index l1 i)}
                      index l1 i == index l (i + n) )))
  =
    let l0, l1 = splitAt n l in
    splitAt_length n l;
    introduce forall (i : dom l0) . index l0 i == index l i
      with lemma_splitAt_reindex_left n l i;
    introduce forall (i : dom l1) . index l1 i == index l (i + n)
      with lemma_splitAt_reindex_right n l i


(* [fold_right] *)

let rec fold_right_append #a #b f l0 l1 x
  : Lemma (ensures fold_right #a #b f (l0@l1) x == fold_right f l0 (fold_right f l1 x))
          (decreases l0)
  = match l0 with
    | [] -> ()
    | hd :: tl -> fold_right_append f tl l1 x


(* [fold_right_gtot] *)

let rec fold_right_gtot_append #a #b l0 l1 f x
  : Lemma (ensures fold_right_gtot #a #b (l0@l1) f x == fold_right_gtot l0 f (fold_right_gtot l1 f x))
          (decreases l0)
  = match l0 with
    | [] -> ()
    | hd :: tl -> fold_right_gtot_append tl l1 f x

let fold_right_gtot_f_comm #a #b (f : a -> b -> GTot b) : prop =
  forall (x0 x1 : a) (y : b) . f x0 (f x1 y) == f x1 (f x0 y)

(* [fold_left] *)

let rec fold_left_ind_aux
      (#a #b : Type) (f : a -> b -> a) (ll : list b) (x : a) (lr : list b)
      (p : (ll : list b) -> (x : a) -> (lr : list b) -> Type0)
      (pf : (ll : list b) -> (x : a) -> (r : b) -> (lr : list b) ->
            Lemma (requires p ll x (r :: lr)) (ensures p (r :: ll) (f x r) lr))
  : Lemma (requires p ll x lr) (ensures p (rev_acc lr ll) (fold_left f x lr) [])
          (decreases lr)
  = match lr with
  | [] -> ()
  | r :: lr ->
      pf ll x r lr;
      fold_left_ind_aux f (r :: ll) (f x r) lr p pf

let fold_left_ind
      (#a #b : Type) (f : a -> b -> a) (x0 : a) (l : list b)
      (p : (ll : list b) -> (x : a) -> (lr : list b) -> Type0)
      (pf : (ll : list b) -> (x : a) -> (r : b) -> (lr : list b) ->
            Lemma (requires p ll x (r :: lr)) (ensures p (r :: ll) (f x r) lr))
  : Lemma (requires p [] x0 l) (ensures p (rev l) (fold_left f x0 l) [])
  = fold_left_ind_aux f [] x0 l p pf

(* [g_for_all] *)

let rec g_for_allP (#a : Type) (l : list a) (f : a -> GTot Type) : prop
  = match l with
    | [] -> True
    | hd :: tl -> f hd /\ g_for_allP tl f

let rec g_for_allP_morph_strong (#a : Type) (l : list a) (f g : a -> GTot Type) :
  Lemma (requires g_for_allP l (fun x -> f x <==> g x))
        (ensures  g_for_allP l f <==> g_for_allP l g)
  = match l with
    | [] -> ()
    | _ :: tl -> g_for_allP_morph_strong tl f g

let rec g_for_allP_True (#a : Type) (l : list a) (f : a -> GTot Type) :
  Lemma (requires forall x. f x) (ensures g_for_allP l f)
  = match l with
    | [] -> ()
    | _ :: tl -> g_for_allP_True tl f

let g_for_allP_morph (#a : Type) (l : list a) (f g : a -> GTot Type) :
  Lemma (requires forall x . f x <==> g x)
        (ensures  g_for_allP l f <==> g_for_allP l g)
  = g_for_allP_True l (fun x -> f x <==> g x);
    g_for_allP_morph_strong l f g

let rec g_for_allP_mem (#a : Type) (l : list a) (f : a -> GTot Type)
  : Lemma (g_for_allP l f <==> (forall x . memP x l ==> f x))
  = match l with
    | [] -> ()
    | _ :: tl -> g_for_allP_mem tl f

let rec g_for_allP_append (#a : Type) (l1 l2 : list a) (f : a -> GTot Type)
  : Lemma (g_for_allP (l1@l2) f <==> g_for_allP l1 f /\ g_for_allP l2 f)
          [SMTPat (g_for_allP #a (l1@l2) f)]
  = match l1 with
    | [] -> ()
    | _ :: tl -> g_for_allP_append tl l2 f

let rec g_for_allP_rev' (#a : Type) (l : list a) (f : a -> GTot Type)
  : Lemma (g_for_allP (rev' l) f <==> g_for_allP l f)
  = match l with
    | [] -> ()
    | hd :: tl ->
      calc (<==>) {
        g_for_allP (rev' l) f;
      <==> {}
        g_for_allP (rev' tl) f /\ g_for_allP [hd] f;
      <==> {g_for_allP_rev' tl f}
        g_for_allP tl f /\ f hd;
      <==> {}
        g_for_allP (hd :: tl) f;
      }

(* [find_gtot] *)

let rec find_gtot (#a:Type) (f:a -> GTot bool) (l:list a) : GTot (option (x:a{f x})) (decreases l)
  = match l with
  | [] -> None
  | hd :: tl -> if f hd then Some #(x:a{f x}) hd else find_gtot f tl
