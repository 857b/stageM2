module Learn.FList

module U    = Learn.Util
module L    = FStar.List.Pure
module Ll   = Learn.List
module Dl   = Learn.DList
module Fin  = FStar.Fin
module Perm = Learn.Permutation
module Fext = FStar.FunctionalExtensionality

// FIXME: some definitions are marked noextract in order to avoid a warning from KRML

(***** Representation of a Dlist as a function *)

unfold let ty_list = Dl.ty_list

type flist (ts : ty_list) : Type =
  Fext.restricted_t (Fin.fin (L.length ts)) (L.index ts)

unfold
let ty (#ts : ty_list) (f : flist ts) = ts

unfold
let mk_flist (ts : ty_list) (f : (i : Fin.fin (L.length ts)) -> L.index ts i)
  : flist ts
  = Fext.on_domain (Fin.fin (L.length ts)) f

let nil : flist []
  = mk_flist [] (fun _ -> false_elim ())

let cons (#t : Type) (x : t) (#ts : ty_list) (xs : flist ts) : flist (t :: ts)
  = mk_flist (t :: ts) (fun i -> if i = 0 then x else U.cast (L.index (t :: ts) i) (xs (i-1)))

let head (#t : Type) (#ts : ty_list) (xs : flist (t :: ts)) : t
  = xs 0

noextract
let tail (#t : Type) (#ts : ty_list) (xs : flist (t :: ts)) : flist ts
  = mk_flist ts (fun i -> U.cast (L.index ts i) (xs (i + 1)))

let flist_extensionality (#ts : ty_list) (xs ys : flist ts)
          (pf : (i : Fin.fin (L.length ts)) -> squash (xs i == ys i))
  : Lemma (ensures xs == ys)
  =
    FStar.Classical.forall_intro_squash_gtot pf;
    Fext.extensionality (Fin.fin (L.length ts)) (L.index ts) xs ys


let flist_of_d (#ts : ty_list) (l : Dl.dlist ts) : flist ts
  = mk_flist ts (Dl.index l)

let dlist_of_f (#ts : ty_list) (f : flist ts) : Dl.dlist ts
  = Dl.initi_ty ts f

let dfd_id (#ts : ty_list) (l : Dl.dlist ts)
  : Lemma (dlist_of_f (flist_of_d l) == l)
          [SMTPat (dlist_of_f (flist_of_d l))]
  = Dl.dlist_extensionality (dlist_of_f (flist_of_d l)) l (fun i -> ())

let fdf_id (#ts : ty_list) (f : flist ts)
  : Lemma (flist_of_d (dlist_of_f f) == f)
          [SMTPat (flist_of_d (dlist_of_f f))]
  = flist_extensionality (flist_of_d (dlist_of_f f)) f (fun i -> ())


noextract
let append (#ts0 #ts1 : ty_list) (xs0 : flist ts0) (xs1 : flist ts1)
  : Tot (flist L.(ts0 @ ts1))
  =
    (**) FStar.Classical.forall_intro (Ll.append_index ts0 ts1);
    mk_flist L.(ts0 @ ts1) (fun i ->
      if i < L.length ts0 then U.cast L.(index (ts0 @ ts1) i) (xs0 i)
                          else U.cast L.(index (ts0 @ ts1) i) (xs1 (i - L.length ts0)))

/// This lemma is only a wrapper around [Ll.append_index]. It is used in place of [Dl.append_index].
let append_index (#ts0 #ts1 : ty_list) (xs0 : flist ts0) (xs1 : flist ts1)
                 (i : Fin.fin (L.length ts0 + L.length ts1))
  : Lemma L.(index (ts0@ts1) i == (if i < length ts0 then index ts0 i else index ts1 (i - length ts0)))
  = Ll.append_index ts0 ts1 i


let splitAt_ty (ts0 ts1 : ty_list) (xs : flist L.(ts0@ts1))
  : Tot (flist ts0 & flist ts1) (decreases ts0)
  = 
    (**) FStar.Classical.forall_intro (Ll.append_index ts0 ts1);
    mk_flist ts0 (fun i -> U.cast (L.index ts0 i) (xs i)),
    mk_flist ts1 (fun i -> U.cast (L.index ts1 i) (xs (L.length ts0 + i)))

let splitAt_ty_of_d (ts0 ts1 : ty_list) (xs : Dl.dlist L.(ts0@ts1))
  : Lemma (splitAt_ty ts0 ts1 (flist_of_d xs)
            == (flist_of_d (Dl.splitAt_ty ts0 ts1 xs)._1, flist_of_d (Dl.splitAt_ty ts0 ts1 xs)._2))
  =
    Dl.splitAt_ty_append ts0 ts1 xs;
    flist_extensionality (splitAt_ty ts0 ts1 (flist_of_d xs))._1
                         (flist_of_d (Dl.splitAt_ty ts0 ts1 xs)._1)
      (fun i -> Dl.append_index (Dl.splitAt_ty ts0 ts1 xs)._1 (Dl.splitAt_ty ts0 ts1 xs)._2 i);
    flist_extensionality (splitAt_ty ts0 ts1 (flist_of_d xs))._2
                         (flist_of_d (Dl.splitAt_ty ts0 ts1 xs)._2)
      (fun i -> Dl.append_index (Dl.splitAt_ty ts0 ts1 xs)._1 (Dl.splitAt_ty ts0 ts1 xs)._2 (L.length ts0 + i))

let splitAt_ty_of_f (ts0 ts1 : ty_list) (xs : flist L.(ts0@ts1))
  : Lemma (Dl.splitAt_ty ts0 ts1 (dlist_of_f xs)
            == (dlist_of_f (splitAt_ty ts0 ts1 xs)._1, dlist_of_f (splitAt_ty ts0 ts1 xs)._2))
  = splitAt_ty_of_d ts0 ts1 (dlist_of_f xs)


(***** permutations *)

noextract
let apply_perm_r (#n : nat) (p : Perm.perm_f n) (#ts : ty_list {L.length ts == n}) (xs : flist ts)
  : flist (Perm.apply_perm_r p ts)
  = mk_flist (Perm.apply_perm_r p ts) (fun i -> U.cast (L.index (Perm.apply_perm_r p ts) i) (xs (p i)))

let apply_r_id_n (len : nat) (#ts : ty_list{L.length ts = len}) (xs : flist ts)
  : Lemma (apply_perm_r (Perm.id_n len) xs == xs) [SMTPat (apply_perm_r (Perm.id_n len) xs)]
  = flist_extensionality (apply_perm_r (Perm.id_n len) xs) xs (fun _ -> ())

let apply_r_comp (#len : nat) (f g : Perm.perm_f len) (#ts : ty_list {L.length ts == len}) (xs : flist ts)
  : Lemma (apply_perm_r (f `Perm.comp` g) xs === apply_perm_r f (apply_perm_r g xs))
  = Perm.apply_r_comp f g ts;
    flist_extensionality (apply_perm_r (f `Perm.comp` g) xs) (apply_perm_r f (apply_perm_r g xs)) (fun _ -> ())

let apply_perm_r_of_d (#n : nat) (p : Perm.perm_f n) (#ts : ty_list {L.length ts == n}) (xs : Dl.dlist ts)
  : Lemma (flist_of_d (Dl.apply_perm_r p xs) == apply_perm_r p (flist_of_d xs))
  = flist_extensionality (flist_of_d (Dl.apply_perm_r p xs)) (apply_perm_r p (flist_of_d xs))
                         (fun i -> ())

let apply_perm_r_of_f (#n : nat) (p : Perm.perm_f n) (#ts : ty_list {L.length ts == n}) (xs : flist ts)
  : Lemma (dlist_of_f (apply_perm_r p xs) == Dl.apply_perm_r p (dlist_of_f xs))
  = Dl.dlist_extensionality (dlist_of_f (apply_perm_r p xs)) (Dl.apply_perm_r p (dlist_of_f xs))
                            (fun i -> ())


unfold
let apply_pequiv (#ts0 #ts1 : ty_list) (f : Perm.pequiv ts0 ts1) (xs : flist ts0) : flist ts1
  = apply_perm_r f xs

let apply_pequiv_sym_l (#ts0 #ts1 : ty_list) (f : Perm.pequiv ts0 ts1) (xs : flist ts0)
  : Lemma (apply_pequiv (Perm.pequiv_sym f) (apply_pequiv f xs) == xs)
  =
    apply_r_comp (Perm.inv_f f) f xs

let apply_pequiv_sym_r (#ts0 #ts1 : ty_list) (f : Perm.pequiv ts0 ts1) (xs : flist ts1)
  : Lemma (apply_pequiv f (apply_pequiv (Perm.pequiv_sym f) xs) == xs)
  =
    Perm.pequiv_as_eq (Perm.pequiv_sym f);
    apply_r_comp f (Perm.inv_f f) xs


let apply_pequiv_sym_eq_iff (#ts0 #ts1 : ty_list) (f : Perm.pequiv ts0 ts1) (xs : flist ts0) (ys : flist ts1)
  : Lemma (xs == apply_pequiv (Perm.pequiv_sym f) ys <==> ys == apply_pequiv f xs)
  =
    apply_pequiv_sym_l f xs;
    apply_pequiv_sym_r f ys


(***** quantifiers *)

let partial_app_flist (src0 : Type u#s) (src : ty_list u#s) (dst : Type u#d) (f : flist (src0 :: src) -> dst)
                      (x : src0) (xs : flist src) : dst
  = f (cons #src0 x #src xs)

let nil_uniq (xs : flist [])
  : Lemma (xs == nil)
  = flist_extensionality xs nil (fun _ -> false_elim ())

let as_cons (#t : Type) (#ts : ty_list) (xs : flist (t :: ts))
  : Lemma (xs == cons #t (head xs) #ts (tail xs))
  = flist_extensionality xs (cons #t (head xs) #ts (tail xs)) (fun _ -> ())

let rec consify (#ts : ty_list) (xs : flist ts)
  : Tot (flist ts) (decreases ts)
  = match ts with
  | []     -> nil
  | t :: ts -> cons (head #t #ts xs) (consify (tail #t #ts xs))

let rec consify_id (#ts : ty_list) (xs : flist ts)
  : Lemma (ensures consify xs == xs) (decreases ts)
          [SMTPat (consify xs)]
  = match ts with
  | []     -> nil_uniq xs
  | t :: ts -> as_cons #t #ts xs;
             consify_id (tail #t #ts xs)


let rec forall_flist (ty : ty_list) (f : flist ty -> Type0)
  : Tot Type0 (decreases ty)
  = match ty with
  | []      -> f nil
  | t0 :: ts -> (forall (x : t0) . forall_flist ts (partial_app_flist t0 ts Type0 f x))

let rec forall_flist_iff (ty : ty_list) (f : flist ty -> Type0)
  : Lemma (ensures forall_flist ty f <==> (forall (xs : flist ty) . f xs)) (decreases ty)
          [SMTPat (forall_flist ty f)]
  = match ty with
  | []      -> FStar.Classical.forall_intro nil_uniq
  | t0 :: ts -> FStar.Classical.forall_intro (as_cons #t0 #ts);
              introduce forall (x : t0) .
                forall_flist ts (partial_app_flist t0 ts Type0 f x) <==>
                (forall (xs : flist ts) . f (cons x xs))
              with forall_flist_iff ts (partial_app_flist t0 ts Type0 f x)


let rec exists_flist (ty : ty_list) (f : flist ty -> Type0)
  : Tot Type0 (decreases ty)
  = match ty with
  | []     -> f nil
  | t0 :: ts -> (exists (x : t0) . exists_flist ts (partial_app_flist t0 ts Type0 f x))

let rec exists_flist_iff (ty : ty_list) (f : flist ty -> Type0)
  : Lemma (ensures exists_flist ty f <==> (exists (xs : flist ty) . f xs)) (decreases ty)
          [SMTPat (exists_flist ty f)]
  = match ty with
  | []      -> FStar.Classical.forall_intro nil_uniq
  | t0 :: ts -> FStar.Classical.forall_intro (as_cons #t0 #ts);
              introduce forall (x : t0) .
                exists_flist ts (partial_app_flist t0 ts Type0 f x) <==>
                (exists (xs : flist ts) . f (cons x xs))
              with exists_flist_iff ts (partial_app_flist t0 ts Type0 f x)


unfold let arw_list = Dl.arw_list

let rec lam_flist (src : ty_list u#s) (dst : Type u#d) (f : flist src -> dst)
  : Tot (arw_list src dst) (decreases src)
  = match src with
  | [] -> Dl.Raise_val (f nil)
  | t0 :: ts -> (fun (x : t0) -> lam_flist ts dst (partial_app_flist t0 ts dst f x))

let rec app_flist (#src : ty_list u#s) (#dst : Type u#d) (f : arw_list src dst) (x : flist src)
  : Tot dst (decreases src)
  = match (|src, f, x|) <: (src : ty_list & arw_list src dst & flist src) with
  | (|[],      v,  _|) -> Dl.downgrade_val v
  | (|t0 :: ts, f, xs|) -> app_flist #ts #dst (f (head xs)) (tail xs)

let rec app_lam_flist (src : ty_list u#s) (dst : Type u#d) (f : flist src -> dst) (x : flist src)
  : Lemma (ensures app_flist (lam_flist src dst f) x == f x)
          (decreases src)
          [SMTPat (app_flist (lam_flist src dst f) x)]
  = match src with
  | []      -> nil_uniq x
  | t0 :: ts -> as_cons #t0 #ts x;
              app_lam_flist ts dst (partial_app_flist t0 ts dst f (head #t0 #ts x)) (tail #t0 #ts x)
