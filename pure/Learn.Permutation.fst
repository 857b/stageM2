module Learn.Permutation

module U    = Learn.Util
module T    = FStar.Tactics
module Fin  = FStar.Fin
module Seq  = FStar.Seq
module Fext = FStar.FunctionalExtensionality

open FStar.Calc
open FStar.Classical.Sugar
open FStar.List.Pure
open Learn.List


(*** [permutation_p] *)

noeq type permutation_p (#a : Type) : list a -> list a -> Type =
  | Perm_swap : l0 : list a -> x : a -> y : a -> l1 : list a ->
              permutation_p (l0 @ x :: y :: l1) (l0 @ y :: x :: l1)
  | Perm_refl  : l : list a -> permutation_p l l
  | Perm_trans : l0 : list a -> l1 : list a -> l2 : list a ->
              permutation_p l0 l1 -> permutation_p l1 l2 ->
              permutation_p l0 l2

type permutation #a l0 l1 = squash (permutation_p #a l0 l1)


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


let rec permutation_p_length #a #l0 #l1 (p : permutation_p #a l0 l1)
  : Lemma (ensures length l0 = length l1) (decreases p)
  = match p with
    | Perm_swap l0 x y l1 -> append_length l0 (x :: y :: l1); append_length l0 (y :: x :: l1)
    | Perm_refl _ -> ()
    | Perm_trans _ _ _ p0 p1 -> permutation_p_length p0; permutation_p_length p1

let rec permutation_p_sym #a l0 l1 (p : permutation_p #a l0 l1)
  : Tot (permutation_p #a l1 l0)
        (decreases p)
  = match p with
    | Perm_refl l -> Perm_refl l
    | Perm_swap l0 x y l1 -> Perm_swap l0 y x l1
    | Perm_trans l0 l1 l2 p0 p1 -> Perm_trans l2 l1 l0 (permutation_p_sym _ _ p1) (permutation_p_sym _ _ p0)

let rec permutation_p_append (#a : Type) (pre l0 l1 sfx : list a) (p : permutation_p l0 l1)
  : Tot (permutation_p (pre @ l0 @ sfx) (pre @ l1 @ sfx))
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
                 Perm_trans _ _ _ (permutation_p_append pre l0 l1 sfx p0)
                                  (permutation_p_append pre l1 l2 sfx p1)

let rec permutation_p_cons_snoc #a x l
  : Tot (permutation_p #a (x :: l) (snoc (l,x)))
        (decreases l)
  = match l with
    | [] -> Perm_refl _
    | hd :: tl ->
      Perm_trans _ _ _ (Perm_swap [] x hd tl)
                       (permutation_p_append [hd] (x :: tl) (snoc (tl,x)) []
                         (permutation_p_cons_snoc #a x tl))
        
let rec permutation_p_rev' #a l
  : Tot (permutation_p #a l (rev' l))
        (decreases l)
  = match l with
    | [] -> Perm_refl _
    | hd :: tl ->
      Perm_trans _ _ _ (permutation_p_cons_snoc hd tl)
                       (permutation_p_append [] tl (rev' tl) [hd]
                         (permutation_p_rev' tl))


let rec fold_right_gtot_comm_permutation_p #a #b l0 l1 f x (p : permutation_p l0 l1)
  : Lemma (requires fold_right_gtot_f_comm #a #b f)
          (ensures fold_right_gtot l0 f x == fold_right_gtot l1 f x)
          (decreases p)
  = match p with
    | Perm_refl _ -> ()
    | Perm_swap l0 x0 x1 l1 ->
                fold_right_gtot_append l0 (x0 :: x1 :: l1) f x;
                fold_right_gtot_append l0 (x1 :: x0 :: l1) f x
    | Perm_trans l0 l1 l2 p0 p1 ->
                fold_right_gtot_comm_permutation_p l0 l1 f x p0;
                fold_right_gtot_comm_permutation_p l1 l2 f x p1


(*** [perm_f] *)

let injective  (#a #b : Type) (f : a -> b) : prop =
  forall (x x' : a) . f x == f x' ==> x == x'

let surjective (#a #b : Type) (f : a -> b) : prop = forall (y : b) . exists (x : a) . f x == y

let inv_l_injective (#a #b : Type) (f : a -> b) (g : b -> a)
  : Lemma (requires forall (x : a) . g (f x) == x) (ensures injective f)
  = ()

let pigeonhole_seq (#n: nat) (s: Seq.seq (Fin.fin n))
  : Pure (Fin.in_ s & Fin.in_ s)
      (requires Seq.length s > n)
      (ensures  fun (i1, i2) -> i1 < i2 /\ Seq.index s i1 = Seq.index s i2)
  = let i1, i2 = Fin.pigeonhole #n (Seq.slice s 0 (n+1)) in i1, i2

let pigeonhole_fun (n m: nat) (f : Fin.fin n -> Fin.fin m)
  : Pure (Fin.fin n & Fin.fin n)
      (requires n > m)
      (ensures  fun (i1, i2) -> i1 < i2 /\ f i1 = f i2)
  = let f_sq = Seq.init n f in
    pigeonhole_seq #m f_sq

let fin_injective_surjective (n m : nat) (f : Fin.fin n -> Fin.fin m)
  : Lemma (requires n >= m /\ injective f) (ensures surjective f)
  =
    introduce forall (y : Fin.fin m) . exists (x : Fin.fin n) . f x == y
    with begin
      let f_sq = Seq.init n f in
      match Fin.find f_sq (fun y' -> y' = y) 0 with
      | Some x -> ()
      | None -> introduce forall i . ~(f i = y)
                 with introduce _ ==> _
                 with _ . assert (Seq.index f_sq i = y);
               let f' (i:Fin.fin n) : Fin.fin (m-1) = if f i > y then f i - 1 else f i in
               let i0, i1 = pigeonhole_fun n (m-1) f' in
               assert False
    end

let surjective_invert_r (#a : eqtype) (n : nat) (f : Fin.fin n -> a)
      (x : a) : Pure (Fin.fin n) (requires surjective f) (ensures fun y -> f y = x)
  =
    let f_sq = Seq.init n f in
    match Fin.find f_sq (fun x' -> x' = x) 0 with
    | Some y -> y
    | None -> eliminate exists y . f y = x
               returns False
               with _ . assert (Seq.index f_sq y = x);
             false_elim ()

let fin_surjective_injective (n m : nat) (f : Fin.fin n -> Fin.fin m)
  : Lemma (requires n <= m /\ surjective f) (ensures injective f)
  = let g : Fin.fin m -> Fin.fin n = surjective_invert_r n f in
    assert (forall (x : Fin.fin m) . {:pattern f (g x)} f (g x) = x);
    fin_injective_surjective m n g;
    introduce forall (y y' : Fin.fin n) . f y = f y' ==> y = y'
      with introduce _ ==> _
      with _ . assert (exists x x' . g x = y /\ g x' = y')


type perm_f (n : nat) = f : Fext.(Fin.fin n ^-> Fin.fin n) {U.hide_prop (injective f)}

let mk_perm_f (n : nat) (f : Fin.fin n -> Fin.fin n)
  : Pure (perm_f n) (requires injective f) (ensures fun _ -> True)
  =
    let p = Fext.on (Fin.fin n) f in
    U.hide_propI (injective p);
    p

let perm_f_extensionality (#n : nat) (f g : perm_f n)
      (pf : (x : Fin.fin n) -> squash (f x = g x))
  : Lemma (ensures  f == g)
  =
    introduce forall (x : Fin.fin n) . f x = g x
      with pf x;
    Fext.extensionality (Fin.fin n) (fun _ -> Fin.fin n) f g

let id_n (n : nat) : perm_f n = mk_perm_f n (fun x -> x)

/// f;g
let comp (#n : nat) (f g : perm_f n) : perm_f n =
  U.hide_propD (injective f); U.hide_propD (injective g);
  mk_perm_f n (fun x -> g (f x))

let comp_assoc (#n : nat) (f g h : perm_f n)
  : Lemma ((f `comp` g) `comp` h == f `comp` (g `comp` h))
  = perm_f_extensionality ((f `comp` g) `comp` h) (f `comp` (g `comp` h)) (fun _ -> ())

let id_nl (#n : nat) (f : perm_f n)
  : Lemma (id_n n `comp` f == f) [SMTPat (id_n n `comp` f)]
  = perm_f_extensionality (id_n n `comp` f) f (fun _ -> ())

let id_nr (#n : nat) (f : perm_f n)
  : Lemma (f `comp` id_n n == f) [SMTPat (f `comp` id_n n)]
  = perm_f_extensionality (f `comp` id_n n) f (fun _ -> ())


let is_inverse (#n : nat) (f : perm_f n) (g : perm_f n) : prop
  = f `comp` g == id_n n  /\  g `comp` f == id_n n

let inverse_intro (#n : nat) (f : perm_f n) (g : perm_f n)
  : Lemma (requires forall (x : Fin.fin n) . f (g x) = x)
          (ensures  is_inverse f g)
  =
    U.hide_propD (injective f);
    Fext.extensionality (Fin.fin n) (fun _ -> Fin.fin n) (fun x -> f (g x)) (id_n n);
    Fext.extensionality (Fin.fin n) (fun _ -> Fin.fin n) (fun x -> g (f x)) (id_n n)

let inv_f (#n : nat) (f : perm_f n)
  : g : perm_f n {is_inverse f g}
  =
    U.hide_propD (injective f);
    fin_injective_surjective n n f;
    let g = mk_perm_f n (surjective_invert_r n f) in
    inverse_intro f g;
    g

let inverse_uniq (#n : nat) (f g0 g1 : perm_f n)
  : Lemma (requires is_inverse f g0 /\ is_inverse f g1)
          (ensures  g0 == g1)
  = assert (f `comp` g0 == f `comp` g1);
    comp_assoc g0 f g0; comp_assoc g0 f g1

let inv_f_id_n (n : nat)
  : Lemma (inv_f (id_n n) == id_n n) [SMTPat (inv_f (id_n n))]
  = inverse_uniq (id_n n) (inv_f (id_n n)) (id_n n)

let inv_f_invol (#n : nat) (f : perm_f n)
  : Lemma (inv_f (inv_f f) == f) [SMTPat (inv_f (inv_f f))]
  = inverse_uniq (inv_f f) (inv_f (inv_f f)) f

let inv_f_comp (#n : nat) (f g : perm_f n)
  : Lemma (inv_f (f `comp` g) == inv_f g `comp` inv_f f)
  =
    comp_assoc f g (inv_f g `comp` inv_f f);
    comp_assoc g (inv_f g) (inv_f f);
    comp_assoc (inv_f g) (inv_f f) (f `comp` g);
    comp_assoc (inv_f f) f g;
    assert (is_inverse (f `comp` g) (inv_f g `comp` inv_f f));
    inverse_uniq (f `comp` g) (inv_f (f `comp` g)) (inv_f g `comp` inv_f f)


let perm_f_of_pair (#n : nat) (f g : Fin.fin n -> Fin.fin n)
  : Pure (perm_f n) (requires forall (x : Fin.fin n) . g (f x) = x)
                    (ensures fun p -> Fext.feq p f /\ Fext.feq (inv_f p) g)
  =
    assert (injective  f);
    assert (surjective g);
    fin_surjective_injective n n g;
    let f_p = mk_perm_f n f in
    let g_p = mk_perm_f n g in
    inverse_intro g_p f_p;
    inverse_uniq f_p (inv_f f_p) g_p;
    f_p

(***** applying a permutation on a list *)

/// l'[i] = l[p[i]]     (right action)
/// p : index l' -> index l
let apply_perm_r (#a : Type) (#len : nat) (p : perm_f len) (l : list a)
  : Pure (list a) (requires length l = len) (ensures fun l' -> length l' = len)
  = initi 0 len (fun i -> index l (p i))

/// l'[p(x)] = l[x]    <==>    l'[y] = l[p^-1(y)]     (left action)
let apply_perm (#a : Type) (#len : nat) (p : perm_f len) (l : list a)
  : Pure (list a) (requires length l = len) (ensures fun l' -> length l' = len)
  = apply_perm_r (inv_f p) l

let apply_r_id_n #a (#len : nat) (l : list a {length l = len})
  : Lemma (apply_perm_r (id_n len) l == l) [SMTPat (apply_perm_r (id_n len) l)]
  = list_extensionality (apply_perm_r (id_n len) l) l (fun _ -> ())

let apply_r_comp #a (#len : nat) (f g : perm_f len) (l : list a {length l = len})
  : Lemma (apply_perm_r (f `comp` g) l == apply_perm_r f (apply_perm_r g l))
  = list_extensionality (apply_perm_r (f `comp` g) l) (apply_perm_r f (apply_perm_r g l)) (fun _ -> ())

let apply_comp #a (#len : nat) (f g : perm_f len) (l : list a {length l = len})
  : Lemma (apply_perm (f `comp` g) l == apply_perm g (apply_perm f l))
  = 
   calc (==) {
      apply_perm (f `comp` g) l;
    == {}
      apply_perm_r (inv_f (f `comp` g)) l;
    == {inv_f_comp f g}
      apply_perm_r (inv_f g `comp` inv_f f) l;
    == {apply_r_comp (inv_f g) (inv_f f) l}
      apply_perm_r (inv_f g) (apply_perm_r (inv_f f) l);
    == {}
      apply_perm g (apply_perm f l);
    }

let map_apply_r (#a #b : Type) (#len : nat) (p : perm_f len) (f : a -> b) (l : list a {length l = len})
  : Lemma (map f (apply_perm_r p l) == apply_perm_r p (map f l))
  =
    list_extensionality (map f (apply_perm_r p l)) (apply_perm_r p (map f l)) (fun _ -> ())


(***** representing a permutation with transpositions / swap *)

let perm_f_transpose (#n : nat) (i j : Fin.fin n) : perm_f n
  =
    let f (x : Fin.fin n) : Fin.fin n
      = if x = i then j else if x = j then i else x
    in perm_f_of_pair f f

let perm_f_transpose_p (#n : nat) (p : Fin.fin n & Fin.fin n) : perm_f n
  = perm_f_transpose p._1 p._2

let perm_f_swap (#n : nat) (i : nat {i <= n - 2}) : perm_f n
  = perm_f_transpose i (i+1)

let perm_f_transpose_inv (#n : nat) (i j : Fin.fin n)
  : Lemma (ensures inv_f (perm_f_transpose i j) == perm_f_transpose i j)
          [SMTPat (inv_f (perm_f_transpose i j))]
  = ()

let perm_f_transpose_sym (#n : nat) (i j : Fin.fin n)
  : Lemma (perm_f_transpose i j == perm_f_transpose j i)
  = perm_f_extensionality (perm_f_transpose i j) (perm_f_transpose j i) (fun _ -> ())


let perm_f_restrict (#n : nat) (f : perm_f (n+1))
  : Pure (perm_f n) (requires f n = n) (ensures fun _ -> True)
  =
    U.hide_propD (injective f);
    mk_perm_f n (fun x -> f x)

let perm_f_extend (#n : nat) (f : perm_f n)
  : perm_f (n+1)
  =
    U.hide_propD (injective f);
    mk_perm_f (n+1) (fun x -> if x = n then n else f x)

let perm_f_extend_restrict (#n : nat) (f : perm_f (n+1))
  : Lemma (requires f n = n) (ensures perm_f_extend (perm_f_restrict f) == f)
          [SMTPat (perm_f_extend (perm_f_restrict f))]
  = perm_f_extensionality (perm_f_extend (perm_f_restrict f)) f (fun _ -> ())

let perm_f_extend_id_n (n : nat)
  : Lemma (perm_f_extend (id_n n) == id_n (n+1)) [SMTPat (perm_f_extend (id_n n))]
  = perm_f_extensionality (perm_f_extend (id_n n)) (id_n (n+1)) (fun _ -> ())

let perm_f_extend_comp (#n : nat) (f g : perm_f n)
  : Lemma (perm_f_extend (f `comp` g) == perm_f_extend f `comp` perm_f_extend g)
          [SMTPat (perm_f_extend (f `comp` g))]
  = perm_f_extensionality (perm_f_extend (f `comp` g)) (perm_f_extend f `comp` perm_f_extend g) (fun _ -> ())

let perm_f_extend_transpose (#n : nat) (i j : Fin.fin n)
  : Lemma (perm_f_extend (perm_f_transpose #n i j) == perm_f_transpose #(n+1) i j)
          [SMTPat (perm_f_extend (perm_f_transpose i j))]
  = perm_f_extensionality (perm_f_extend (perm_f_transpose i j)) (perm_f_transpose #(n+1) i j) (fun _ -> ())

/// comp_list [f0; f1 ...] = f0; (f1; ...)
let comp_list (#n : nat) (fs : list (perm_f n)) : perm_f n
  = fold_right comp fs (id_n n)

let rec comp_list_append (#n : nat) (fs0 fs1 : list (perm_f n))
  : Lemma (ensures comp_list (fs0 @ fs1) == comp_list fs0 `comp` comp_list fs1)
          (decreases fs0)
  = match fs0 with
    | [] -> ()
    | hd :: tl -> comp_list_append tl fs1;
                comp_assoc hd (comp_list tl) (comp_list fs1)

let rec perm_f_extend_comp_list (#n : nat) (fs : list (perm_f n))
  : Lemma (ensures perm_f_extend (comp_list fs) == comp_list (map perm_f_extend fs))
          (decreases fs)
  = match fs with
    | [] -> ()
    | f :: fs -> perm_f_extend_comp_list fs

let rec extend_transpose_comp_list (#n : nat) (l : list (Fin.fin n & Fin.fin n))
  : Pure (list (Fin.fin (n+1) & Fin.fin (n+1)))
         (requires True)
         (ensures fun l' -> perm_f_extend (comp_list (map perm_f_transpose_p l))
                         == comp_list (map perm_f_transpose_p l'))
         (decreases l)
  = match l with
    | [] -> []
    | (i,j) :: tl -> (i,j) :: extend_transpose_comp_list tl


let rec perm_f_to_transpose (#n : nat) (f : perm_f n)
  : Pure (list (Fin.fin n & Fin.fin n)) (requires True)
         (ensures fun l -> f == comp_list (map perm_f_transpose_p l))
         (decreases n)
  =
    if n = 0 then begin
      perm_f_extensionality #0 (U.cast (perm_f 0) f) (id_n 0) (fun _ -> ());
      []
    end else begin
      let n  = n - 1 in
      let f  = U.cast (perm_f (n+1)) f in
      let ft = f `comp` perm_f_transpose (f n) n in
      let fr = perm_f_restrict ft in
      let l  = perm_f_to_transpose fr in
      let l' = extend_transpose_comp_list l @ [f n, n] in
      calc (==) {
        f;
      == {comp_assoc f (perm_f_transpose (f n) n) (perm_f_transpose (f n) n);
          perm_f_transpose_inv (f n) n}
        ft `comp` perm_f_transpose (f n) n;
      == {}
        perm_f_extend (comp_list (map perm_f_transpose_p l)) `comp` perm_f_transpose (f n) n;
      == {}
        comp_list (map perm_f_transpose_p (extend_transpose_comp_list l))
          `comp` comp_list (map perm_f_transpose_p [f n, n]);
      == {comp_list_append (map perm_f_transpose_p (extend_transpose_comp_list l))
                           (map perm_f_transpose_p [f n, n]);
          map_append perm_f_transpose_p (extend_transpose_comp_list l) [f n, n]}
        comp_list (map perm_f_transpose_p l');
      };
      l'
    end

#push-options "--z3rlimit 10"
let perm_f_transpose_itm (#n : nat) (i j k : Fin.fin n)
  : Lemma (requires j <> k /\ j <> i)
          (ensures perm_f_transpose i j ==
                   perm_f_transpose i k `comp` perm_f_transpose k j `comp` perm_f_transpose i k)
  = perm_f_extensionality
          (perm_f_transpose i j)
          (perm_f_transpose i k `comp` perm_f_transpose k j `comp` perm_f_transpose i k)
          (fun _ -> ())
#pop-options

let rec perm_f_transpose_to_swap_aux (#n : nat) (i j : Fin.fin n)
  : Pure (list (k : nat {k <= n-2})) (requires i <= j)
         (ensures fun l -> perm_f_transpose i j == comp_list (map perm_f_swap l))
         (decreases j-i)
  = if j = i
    then begin
      perm_f_extensionality (perm_f_transpose i i) (id_n n) (fun _ -> ());
      []
    end else if j = i + 1
    then [i]
    else begin
      let sw = perm_f_swap #n i in
      let l = perm_f_transpose_to_swap_aux (i+1) j in
      calc (==) {
        perm_f_transpose i j;
      == {perm_f_transpose_itm i j (i+1)}
        sw `comp` perm_f_transpose (i+1) j `comp` sw;
      == {}
        (comp_list (map perm_f_swap [i]) `comp` comp_list (map perm_f_swap l)) `comp`
        comp_list (map perm_f_swap [i]);
      == {comp_list_append (map perm_f_swap [i]) (map (perm_f_swap #n) l);
          map_append (perm_f_swap #n) [i] l;
          comp_list_append (map perm_f_swap (i :: l)) (map (perm_f_swap #n) [i]);
          map_append (perm_f_swap #n) (i :: l) [i] }
        comp_list (map perm_f_swap (i :: l @ [i]));
      };
      i :: l @ [i]
    end

let perm_f_transpose_to_swap (#n : nat) (i j : Fin.fin n)
  : Pure (list (k : nat {k <= n-2})) (requires True)
         (ensures fun l -> perm_f_transpose i j == comp_list (map perm_f_swap l))
  = if i <= j then perm_f_transpose_to_swap_aux i j
    else (perm_f_transpose_sym i j; perm_f_transpose_to_swap_aux j i)

let rec perm_f_transpose_list_to_swap (#n : nat) (ts : list (Fin.fin n & Fin.fin n))
  : Pure (list (k : nat {k <= n-2})) (requires True)
         (ensures fun l -> comp_list (map perm_f_transpose_p ts) == comp_list (map perm_f_swap l))
  = match ts with
    | [] -> []
    | hd :: tl -> let lhd = perm_f_transpose_to_swap hd._1 hd._2 in
                let ltl = perm_f_transpose_list_to_swap tl     in
                comp_list_append (map perm_f_swap lhd) (map (perm_f_swap #n) ltl);
                map_append (perm_f_swap #n) lhd ltl;
                lhd @ ltl

let perm_f_to_swap (#n : nat) (f : perm_f n)
  : Pure (list (k : nat {k <= n-2})) (requires True)
         (ensures fun l -> f == comp_list (map perm_f_swap l))
  = perm_f_transpose_list_to_swap (perm_f_to_transpose f)


(***** [perm_f] to [permutation_p] *)

/// effect of a swap on a list
let rec list_swap (#a : Type) (i : nat) (l : list a)
  : Pure (list a) (requires i <= length l - 2) (ensures fun l' -> length l' = length l)
         (decreases i)
  = if i = 0
    then let x :: y :: tl = l in y :: x :: tl
    else let hd :: tl = l    in hd :: list_swap (i-1) tl

let perm_f_shift (#len : nat) (p : perm_f len) : perm_f (len+1)
  = 
    U.hide_propD (injective p);
    mk_perm_f (len+1) (fun i -> (if i = 0 then 0 else p (i-1) + 1))

let apply_perm_f_shift (#a : Type) (#len : nat) (p : perm_f len) (hd : a) (tl : list a{length tl = len})
  : Lemma (apply_perm_r (perm_f_shift p) (hd :: tl) == hd :: apply_perm_r p tl)
  = list_extensionality (apply_perm_r (perm_f_shift p) (hd :: tl)) (hd :: apply_perm_r p tl) (fun _ -> ())

let perm_f_swap_rec_rel (len : nat) (i : nat {i <= len - 2})
  : Lemma (perm_f_swap #(len+1) (i+1) == perm_f_shift (perm_f_swap #len i))
  = perm_f_extensionality (perm_f_swap #(len+1) (i+1)) (perm_f_shift (perm_f_swap #len i)) (fun _ -> ())

#push-options "--z3rlimit 20"
let rec apply_swap_as_rec (#a : Type) (len : nat) (i : nat {i <= len-2}) (l : list a {length l = len})
  : Lemma (ensures apply_perm_r (perm_f_swap #len i) l == list_swap i l)
          (decreases len)
  = if i = 0 then begin
       let x :: y :: tl = l in
       list_extensionality (apply_perm_r (perm_f_swap #len 0) (x :: y :: tl)) (y :: x :: tl) (fun _ -> ())
    end else begin
      let hd :: tl = l in
      perm_f_swap_rec_rel (len-1) (i-1);
      apply_perm_f_shift (perm_f_swap #(len-1) (i-1)) hd tl;
      apply_swap_as_rec (len-1) (i-1) tl
    end
#pop-options

let rec list_swap_splitted (#a : Type) (i : nat) (l0 : list a) (x y : a) (l1 : list a)
  : Lemma (requires length l0 = i)
          (ensures  i <= length (l0 @ x :: y :: l1) - 2 /\
                    list_swap i (l0 @ x :: y :: l1) == (l0 @ y :: x :: l1))
          (decreases i)
  = if i = 0 then () else list_swap_splitted (i-1) (tl l0) x y l1

let apply_swap_splitted (#a : Type) (len : nat) (i : nat{i <= len-2})
      (l0 : list a) (x y : a) (l1 : list a)
  : Lemma (requires length (l0 @ x :: y :: l1) = len /\ length l0 = i)
          (ensures  apply_perm_r (perm_f_swap #len i) (l0 @ x :: y :: l1) == l0 @ y :: x :: l1)
  =
    apply_swap_as_rec len i (l0 @ x :: y :: l1);
    list_swap_splitted i l0 x y l1

let apply_swap_split (#a : Type) (len : nat) (i : nat{i <= len-2}) (l : list a)
  : Pure (list a & a & a & list a)
      (requires length l = len)
      (ensures fun (l0, x, y, l1) ->
               length l0 = i /\
               l == l0 @ x :: y :: l1 /\
               apply_perm_r (perm_f_swap #len i) l == l0 @ y :: x :: l1)
  =
    let l0, l10 = splitAt i l in
    splitAt_length i l;
    let x :: y :: l1 = l10 in
    lemma_splitAt_append i l;
    apply_swap_splitted len i l0 x y l1;
    l0,x,y,l1

let apply_swap_p (#a : Type) (#len : nat) (i : nat{i <= len-2}) (l : list a {length l = len})
  : permutation_p l (apply_perm_r (perm_f_swap #len i) l)
  =
    let l0,x,y,l1 = apply_swap_split len i l in
    Perm_swap l0 x y l1

let rec apply_swap_list_p (#a : Type) (#len : nat) (il : list (k : nat{k <= len-2})) (l : list a {length l = len})
  : Tot (permutation_p l (apply_perm_r (comp_list (map (perm_f_swap #len) il)) l))
        (decreases il)
  = match il with
  | [] -> Perm_refl l
  | hd :: tl ->
       let l1 = apply_perm_r (comp_list (map (perm_f_swap #len) tl)) l in
       apply_r_comp (perm_f_swap #len hd) (comp_list (map (perm_f_swap #len) tl)) l;
       Perm_trans l l1 _ (apply_swap_list_p tl l) (apply_swap_p hd l1)

let apply_perm_p (#a : Type) (#len : nat) (p : perm_f len) (l : list a {length l = len})
  : permutation_p l (apply_perm_r p l)
  = apply_swap_list_p (perm_f_to_swap p) l


(***** [pequiv] *)

type pequiv (#a : Type) (l0 l1 : list a) =
  f : perm_f (length l0) { l1 == apply_perm_r f l0 }

let pequiv_as_eq #a (#l0 #l1 : list a) (f : pequiv l0 l1)
  : Lemma (l1 == apply_perm_r f l0)
  = ()

unfold
let pequiv_sym #a (#l0 #l1 : list a) (f : pequiv l0 l1) : pequiv l1 l0
  =
    (**) apply_r_comp (inv_f f) f l0;
    U.cast #(perm_f (length l0)) (perm_f (length l1)) (inv_f f)


(*** [perm_t] *)

/// representation of the permutation that maps [i] to [index l i]
type perm_t (len : nat) : Type =
  l : list (i : nat {i < len}) { length l = len(*Redundant but useful*) /\ (forall (i : nat {i < len}) . count i l = 1) }

(*
let perm_t_to_fun (#len : nat) (p : perm_t len) : i:nat{i<len} -> i:nat{i<len}
  = index p

let rec findi (#a : Type) (f : a -> bool) (l : list a)
  : Pure nat (requires existsb f l) (ensures fun i -> i < length l /\ f (index l i))
  = let x :: xs = l in
    if f x then 0
    else findi f xs + 1

let rec index_mem (#a : eqtype) (l : list a) (i : nat{i < length l})
  : Lemma (ensures mem (index l i) l) (decreases i)
  = let _ :: tl = l in
    if i = 0 then () else index_mem tl (i - 1)

let rec count_one (#a : eqtype) (x : a) (l : list a) (i0 i1 : (i:nat{i < length l /\ index l i = x}))
  : Lemma (requires count x l <= 1) (ensures i0 = i1) (decreases l)
  = let _ :: tl = l in
    if i0 = 0 && i1 = 0 then ()
    else if i0 > 0 && i1 > 0 then count_one x tl (i0 - 1) (i1 - 1)
    else begin
      mem_count tl x;
      if i0 > 0 then index_mem tl (i0 - 1);
      if i1 > 0 then index_mem tl (i1 - 1);
      assert False
    end

let rec count_one_r (#a : eqtype) (x : a) (l : list a)
  : Lemma (requires forall (i0 i1 : (i:nat{i < length l /\ index l i = x})) . i0 = i1)
          (ensures count x l <= 1)
          (decreases l)
  = match l with
  | [] -> ()
  | hd :: tl ->
      if hd = x then begin
        if count x tl = 0 then ()
        else begin
          mem_count tl x; mem_existsb (fun y -> y = x) tl;
          let i1 = findi (fun y -> y = x) tl in
          eliminate forall (i0 i1 : (i:nat{i < length l /\ index l i = x})) . i0 = i1
            with 0 (i1+1)
        end
      end else begin
        introduce forall (i0 i1 : (i:nat{i < length tl /\ index tl i = x})) . i0 = i1
          with eliminate forall (i0 i1 : (i:nat{i < length l /\ index l i = x})) . i0 = i1
          with (i0+1) (i1+1);
        count_one_r x tl
      end


let perm_t_to_fun_inv (#len : nat) (p : perm_t len) : i:nat{i<len} -> j:nat{j<len /\ perm_t_to_fun p j = i}
  = fun i -> mem_count p i; mem_existsb (fun i' -> i' = i) p;
          findi (fun i' -> i' = i) p

/// This direction is given by the refinement on the result type of [perm_t_to_fun_inv]
let perm_t_to_fun_inv_r (#len : nat) (p : perm_t len) (i : nat{i < len})
  : Lemma (perm_t_to_fun p (perm_t_to_fun_inv p i) = i)
  = ()

let perm_t_to_fun_inv_l (#len : nat) (p : perm_t len) (i : nat{i < len})
  : Lemma (perm_t_to_fun_inv p (perm_t_to_fun p i) = i)
          [SMTPat (perm_t_to_fun_inv p (perm_t_to_fun p i))]
  = count_one (index p i) p i (perm_t_to_fun_inv p (perm_t_to_fun p i))


let perm_t_of_fun_inj (len : nat) (f : (i:nat{i<len}) -> (i:nat{i<len}))
  : Pure (perm_t len) (requires injective f)
                      (ensures fun p -> Fext.feq (perm_t_to_fun p) f)
  = let p = initi 0 len f in
    introduce forall (y : nat {y < len}) . count y p = 1
      with begin
           count_one_r y p;
           fin_injective_surjective len f;
           eliminate exists (x : nat {x < len}) . f x = y
             returns mem y p
             with _ . index_mem p x;
           mem_count p y
      end;
    p

let perm_t_of_fun (len : nat) (f : (i:nat{i<len}) -> (i:nat{i<len})) (g : (i:nat{i<len}) -> (i:nat{i<len}))
  : Pure (perm_t len) (requires forall (i:nat{i<len}) . g (f i) == i)
                      (ensures fun p -> Fext.feq (perm_t_to_fun p) f)
  = inv_l_injective f g;
    perm_t_of_fun_inj len f


let invert_perm (#len : nat) (p : perm_t len) : r : perm_t len { Fext.feq (perm_t_to_fun r) (perm_t_to_fun_inv p) }
  = perm_t_of_fun len (perm_t_to_fun_inv p) (perm_t_to_fun p)


/// classical permutation application:
/// l'[p(x)] = l[x]    <==>    l'[y] = l[p^-1(y)]
let apply_perm (#a : Type) (#len : nat) (p : perm_t len) (l : list a)
  : Pure (list a) (requires length l = len) (ensures fun l' -> length l' = len)
  =
    let f (i : nat {i < len}) = index l (perm_t_to_fun_inv p i) in
    initi 0 len f

let apply_index_map (#a : Type) (len : nat) (idxs : list (i : nat {i < len})) (l : list a)
  : Pure (list a) (requires length l = len) (ensures fun l' -> length l' = length idxs)
  =
    let len' = length idxs in
    let f (i : nat {i < len'}) = index l (index idxs i) in
    initi 0 len' f

/// l'[i] = l[p[i]]
let apply_perm_r (#a : Type) (#len : nat) (p : perm_t len) (l : list a)
  : Pure (list a) (requires length l = len) (ensures fun l' -> length l' = len)
  = apply_index_map len p l

let apply_perm_r_idx (#a : Type) (#len : nat) (p : perm_t len) (l : list a) (i : nat {i < len})
  : Lemma (requires length l = len)
          (ensures  index (apply_perm_r p l) i == index l (index p i))
  = ()

let apply_perm_eq_r (#a : Type) (#len : nat) (p : perm_t len) (l : list a {length l = len})
  : Lemma (apply_perm p l == apply_perm_r (invert_perm p) l)
  = index_extensionality (apply_perm p l) (apply_perm_r (invert_perm p) l)

/// p0; p1  i.e.  x |-> p1 (p0 x)
let compose_perm (#len : nat) (p0 p1 : perm_t len)
  : Tot (perm_t len)
  = let p x = perm_t_to_fun p1 (perm_t_to_fun p0 x) in
    let p_inv y = perm_t_to_fun_inv p0 (perm_t_to_fun_inv p1 y) in
    perm_t_of_fun len p p_inv

let invert_compose_perm (#len : nat) (p0 p1 : perm_t len)
  : Lemma (invert_perm (compose_perm p0 p1) = compose_perm (invert_perm p1) (invert_perm p0))
  = index_extensionality (invert_perm (compose_perm p0 p1)) (compose_perm (invert_perm p1) (invert_perm p0))

let compose_perm_as_apply_r (#len : nat) (p0 p1 : perm_t len)
  : Lemma (compose_perm p0 p1 == apply_perm_r p0 p1)
  = index_extensionality (compose_perm p0 p1) (apply_perm_r p0 p1)

let apply_r_compose_perm (#a : Type) (#len : nat) (p0 p1 : perm_t len) (l : list a)
  : Lemma (requires length l == len)
          (ensures  apply_perm_r (compose_perm p0 p1) l == apply_perm_r p0 (apply_perm_r p1 l))
  =
    introduce forall (i : nat {i < len}).
        index (apply_perm_r (compose_perm p0 p1) l) i == index (apply_perm_r p0 (apply_perm_r p1 l)) i
      with begin
        calc (==) {
          index (apply_perm_r (compose_perm p0 p1) l) i;
        == {}
          index l (index (compose_perm p0 p1) i);
        == {}
          index l (index p1 (index p0 i));
        };
        calc (==) {
          index (apply_perm_r p0 (apply_perm_r p1 l)) i;
        == {}
          index (apply_perm_r p1 l) (index p0 i);
        == {apply_perm_r_idx p1 l (index p0 i)}
          index l (index p1 (index p0 i));
        }
      end;
    index_extensionality (apply_perm_r (compose_perm p0 p1) l) (apply_perm_r p0 (apply_perm_r p1 l))

let apply_compose_perm (#a : Type) (#len : nat) (p0 p1 : perm_t len) (l : list a)
  : Lemma (requires length l == len)
          (ensures  apply_perm (compose_perm p0 p1) l == apply_perm p1 (apply_perm p0 l))
  =
  calc (==) {
    apply_perm (compose_perm p0 p1) l;
  == {apply_perm_eq_r (compose_perm p0 p1) l}
    apply_perm_r (invert_perm (compose_perm p0 p1)) l;
  == {invert_compose_perm p0 p1}
    apply_perm_r (compose_perm (invert_perm p1) (invert_perm p0)) l;
  == {apply_r_compose_perm (invert_perm p1) (invert_perm p0) l}
    apply_perm_r (invert_perm p1) (apply_perm_r (invert_perm p0) l);
  == {apply_perm_eq_r p0 l; apply_perm_eq_r p1 (apply_perm p0 l)}
    apply_perm p1 (apply_perm p0 l);
  }


let perm_id_f (len : nat) (j:nat{j<len}) : j:nat{j<len}
  = j

let perm_id (len : nat)
  : Pure (perm_t len) (requires True)
         (ensures fun p -> Fext.feq (perm_t_to_fun p) (perm_id_f len))
  = perm_t_of_fun len (perm_id_f len) (perm_id_f len)

let perm_id_apply (#a : Type) (len : nat) (l : list a)
  : Lemma (requires length l = len)
          (ensures  apply_perm (perm_id len) l == l)
          [SMTPat (apply_perm (perm_id len) l)]
  =
    index_extensionality (apply_perm (perm_id len) l) l



let perm_swap_f (len : nat) (i : nat{i<=len-2}) (j:nat{j<len}) : j:nat{j<len}
  = if j = i then i+1 else if j=i+1 then i else j

let perm_swap (len : nat) (i : nat)
  : Pure (perm_t len) (requires i <= len - 2)
         (ensures fun p -> Fext.feq (perm_t_to_fun p) (perm_swap_f len i))
  = perm_t_of_fun len (perm_swap_f len i) (perm_swap_f len i)

#push-options "--z3rlimit 60"
(* The verification time varies a lot. TODO: more robust proof *)
let perm_swap_apply_r (#a : Type) (len : nat) (i : nat) (l0 : list a) (x y : a) (l1 : list a)
  : Lemma (requires length l0 = i /\ length l0 + length l1 + 2 = len)
          (ensures  length (l0 @ x :: y :: l1) = len /\
                    apply_perm_r (perm_swap len i) (l0 @ x :: y :: l1) == l0 @ y :: x :: l1)
  = append_length l0 (x :: y :: l1);
    append_length l0 (y :: x :: l1);
    introduce forall (j : nat) . j < len ==>
              index (apply_perm_r (perm_swap len i) (l0 @ x :: y :: l1)) j == index (l0 @ y :: x :: l1) j
      with introduce _ ==> _
      with _. (append_index l0 (y :: x :: l1) j;
               let r = index (apply_perm_r (perm_swap len i) (l0 @ x :: y :: l1)) j in
               assert (r == index (l0 @ x :: y :: l1) (perm_swap_f len i j));
               append_index l0 (x :: y :: l1) (perm_swap_f len i j);
               if j < i        then assert (r == index l0 j)
               else if j = i   then assert (r == y)
               else if j = i+1 then assert (r == x)
               else assert (r == index l1 (j-i-2))
               );
    index_extensionality (apply_perm_r (perm_swap len i) (l0 @ x :: y :: l1)) (l0 @ y :: x :: l1)
#pop-options
*)
