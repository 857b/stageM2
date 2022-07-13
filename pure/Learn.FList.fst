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

let nil_uniq (xs : flist [])
  : Lemma (xs == nil)
  = flist_extensionality xs nil (fun _ -> false_elim ())

let as_cons (#t : Type) (#ts : ty_list) (xs : flist (t :: ts))
  : Lemma (xs == cons #t (head xs) #ts (tail xs))
  = flist_extensionality xs (cons #t (head xs) #ts (tail xs)) (fun _ -> ())

let tail_cons (#t : Type) (#ts : ty_list) (x : t) (xs : flist ts)
  : Lemma (tail (cons x xs) == xs)
  = flist_extensionality (tail (cons x xs)) xs (fun _ -> ())


let flist_of_d (#ts : ty_list) (l : Dl.dlist ts) : flist ts
  = mk_flist ts (Dl.index l)

let rec flist_of_d' (#ts : ty_list) (l : Dl.dlist ts)
  : Tot (flist ts) (decreases l)
  = match l with
  | Dl.DNil -> nil
  | Dl.DCons _ x0 _ xs -> let f = flist_of_d' xs in cons x0 f

let rec flist_of_d'_eq (#ts : Dl.ty_list) (l : Dl.dlist ts)
  : Lemma (ensures flist_of_d' l == flist_of_d l) (decreases l)
          [SMTPat (flist_of_d' l)]
  = match l with
  | Dl.DNil -> nil_uniq (flist_of_d l)
  | Dl.DCons t0 x0 ts xs ->
              flist_of_d'_eq xs;
              flist_extensionality (cons x0 (flist_of_d' xs)) (flist_of_d l) (fun i -> ())

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

let dlist_of_f_cons (#t : Type) (x : t) (#ts : ty_list) (xs : flist ts)
  : Lemma (dlist_of_f (cons x xs) == Dl.DCons t x ts (dlist_of_f xs))
  = Dl.dlist_extensionality (dlist_of_f (cons x xs)) (Dl.DCons t x ts (dlist_of_f xs)) (fun i -> ())


let flist_eq2 (#ts : ty_list) (f g : flist ts) : prop
  = Dl.dlist_eq2 (dlist_of_f f) (dlist_of_f g)

let flist_eq2_spec (#ts : ty_list) (f g : flist ts)
  : Lemma (flist_eq2 f g <==> f == g)
  =
    Dl.dlist_eq2_spec (dlist_of_f f) (dlist_of_f g);
    fdf_id f; fdf_id g

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

let append_nil_l
      (#ts : ty_list) (xs : flist ts)
  : Lemma (append nil xs == xs)
          [SMTPat (append nil xs)]
  = flist_extensionality (append nil xs) xs (fun i -> ())

let append_nil_r
      (#ts : ty_list) (xs : flist ts)
  : Lemma (append xs nil == xs)
          [SMTPat (append xs nil)]
  = flist_extensionality (append xs nil) xs (fun i -> ())

let append_assoc (#t0 #t1 #t2 : ty_list) (x0 : flist t0) (x1 : flist t1) (x2 : flist t2)
  : Lemma (append x0 (append x1 x2) === append (append x0 x1) x2)
  =
    L.append_assoc t0 t1 t2;
    flist_extensionality (append x0 (append x1 x2)) (append (append x0 x1) x2) (fun i -> ())

let dlist_of_f_append
      (#ts0 #ts1 : ty_list) (xs0 : flist ts0) (xs1 : flist ts1)
  : Lemma (dlist_of_f (append xs0 xs1)
        == Dl.append (dlist_of_f xs0) (dlist_of_f xs1))
  = Dl.dlist_extensionality
      (dlist_of_f (append xs0 xs1))
      (Dl.append (dlist_of_f xs0) (dlist_of_f xs1))
      (fun i -> Dl.append_index (dlist_of_f xs0) (dlist_of_f xs1) i;
             append_index xs0 xs1 i)


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

let splitAt_ty_append (ts0 ts1 : ty_list) (xs : flist L.(ts0@ts1))
  : Lemma (let (xs0, xs1) = splitAt_ty ts0 ts1 xs in xs == append xs0 xs1)
  = let (xs0, xs1) = splitAt_ty ts0 ts1 xs in
    flist_extensionality xs (append xs0 xs1) (fun i -> ())

let append_splitAt_ty (ts0 ts1 : ty_list) (xs0 : flist ts0) (xs1 : flist ts1)
  : Lemma (splitAt_ty ts0 ts1 (append xs0 xs1) == (xs0, xs1))
  =
    let (xs0', xs1') = splitAt_ty ts0 ts1 (append xs0 xs1) in
    flist_extensionality xs0' xs0 (fun i -> ());
    flist_extensionality xs1' xs1 (fun i -> ())

(***** ghost *)

type flist_g (ts : ty_list) : Type =
  Fext.restricted_g_t (Fin.fin (L.length ts)) (L.index ts)

unfold
let mk_flist_g (ts : ty_list) (f : (i : Fin.fin (L.length ts)) -> GTot (L.index ts i))
  : flist_g ts
  = Fext.on_domain_g (Fin.fin (L.length ts)) f

let flist_g_extensionality (#ts : ty_list) (xs ys : flist_g ts)
          (pf : (i : Fin.fin (L.length ts)) -> squash (xs i == ys i))
  : Lemma (ensures xs == ys)
  =
    FStar.Classical.forall_intro_squash_gtot pf;
    Fext.extensionality_g (Fin.fin (L.length ts)) (L.index ts) xs ys


let dlist_of_f_g (#ts : ty_list) (f : flist_g ts) : GTot (Dl.dlist ts)
  = Dl.initi_ty_g ts f

let flist_g_of_d (#ts : ty_list) (l : Ghost.erased (Dl.dlist ts)) : flist_g ts
  = mk_flist_g ts (Dl.index l)

let dfd_g_id (#ts : ty_list) (l : Dl.dlist ts)
  : Lemma (dlist_of_f_g (flist_g_of_d l) == l)
          [SMTPat (dlist_of_f_g (flist_g_of_d l))]
  = Dl.dlist_extensionality (dlist_of_f_g (flist_g_of_d l)) l (fun i -> ())

let fdf_g_id (#ts : ty_list) (f : flist_g ts)
  : Lemma (flist_g_of_d (dlist_of_f_g f) == f)
          [SMTPat (flist_g_of_d (dlist_of_f_g f))]
  = flist_g_extensionality (flist_g_of_d (dlist_of_f_g f)) f (fun i -> ())


let flist_to_g (#ts : ty_list) (f : Ghost.erased (flist ts))
  : flist_g ts
  = mk_flist_g ts (fun i -> Ghost.reveal f i)

/// Since the domain [Fin.fin n] is finite, it is possible to obtain [GTot (Fin.fin n -> _)]
/// from [Fin.fin n -> GTot _]
let flist_of_g (#ts : ty_list) (f : flist_g ts)
  : GTot (flist ts)
  = flist_of_d (dlist_of_f_g f)

let gfg_id (#ts : ty_list) (f : flist_g ts)
  : Lemma (flist_to_g (flist_of_g f) == f)
          [SMTPat (flist_to_g (flist_of_g f))]
  = flist_g_extensionality (flist_to_g (flist_of_g f)) f (fun i -> ())

let fgf_id (#ts : ty_list) (f : flist ts)
  : Lemma (flist_of_g (flist_to_g f) == f)
          [SMTPat (flist_of_g (flist_to_g f))]
  = flist_extensionality (flist_of_g (flist_to_g f)) f (fun i -> ())

let flist_of_g_id (#ts : ty_list) (f : flist_g ts) (i : Fin.fin (L.length ts))
  : Lemma (flist_of_g f i == f i)
  = ()

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

let apply_perm_r_inj (#n : nat) (p : Perm.perm_f n) (#ts : Ll.vec n Type) (xs ys : flist ts)
  : Lemma (requires apply_perm_r p xs == apply_perm_r p ys)
          (ensures  xs == ys)
  = assert (apply_perm_r (Perm.inv_f p) (apply_perm_r p xs)
         == apply_perm_r (Perm.inv_f p) (apply_perm_r p ys));
    apply_r_comp (Perm.inv_f p) p xs;
    apply_r_comp (Perm.inv_f p) p ys


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

#push-options "--ifuel 0 --fuel 0"
let apply_pequiv_trans
      (#t0 #t1 #t2 : ty_list) (f : Perm.pequiv t0 t1) (g : Perm.pequiv t1 t2) (xs : flist t0)
  : Lemma (apply_pequiv (Perm.pequiv_trans f g) xs == apply_pequiv g (apply_pequiv f xs))
  = apply_r_comp (Perm.perm_cast _ g) f xs

let apply_pequiv_append
      (#t0 #t0' #t1 #t1' : ty_list) (f0 : Perm.pequiv t0 t0') (f1 : Perm.pequiv t1 t1')
      (xs0 : flist t0) (xs1 : flist t1)
  : Lemma (apply_pequiv (Perm.pequiv_append f0 f1) (append xs0 xs1)
       == append (apply_pequiv f0 xs0) (apply_pequiv f1 xs1))
  = flist_extensionality
       (apply_pequiv (Perm.pequiv_append f0 f1) (append xs0 xs1))
       (append (apply_pequiv f0 xs0) (apply_pequiv f1 xs1))
       (fun i -> ())
#pop-options


(***** quantifiers *)

let partial_app_flist (src0 : Type u#s) (src : ty_list u#s) (dst : Type u#d) (f : flist (src0 :: src) -> dst)
                      (x : src0) (xs : flist src) : dst
  = f (cons #src0 x #src xs)

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


(****** Quantifying on a part of a list *)

// ALT? Mask

type partial_eq_t (ty : ty_list) =
  Dl.dlist (L.map option ty)

let partial_eq (#ty : ty_list) (f : flist ty) (e : partial_eq_t ty) : prop =
  forall (i : Fin.fin (L.length ty) {Some? #(L.index ty i) (Dl.index e i)}) . f i == Some?.v (Dl.index e i)

let partial_app_flist_eq_Some
      (src0 : Type u#s) (src : ty_list u#s) (dst : Type u#d) (x : src0) (e : partial_eq_t src)
      (f : (l : flist (src0 :: src) {partial_eq l (Dl.DCons _ (Some x) _ e)}) -> dst)
      (xs : flist src {partial_eq xs e} ) : dst
  = f (cons #src0 x #src xs)

let partial_app_flist_eq_None
      (src0 : Type u#s) (src : ty_list u#s) (dst : Type u#d) (x : src0) (e : partial_eq_t src)
      (f : (l : flist (src0 :: src) {partial_eq l (Dl.DCons _ None _ e)}) -> dst)
      (xs : flist src {partial_eq xs e} ) : dst
  = f (cons #src0 x #src xs)


let rec forall_flist_part (ty : ty_list) (e : partial_eq_t ty) (p : (f : flist ty {partial_eq f e}) -> Type0)
  : Tot Type0 (decreases ty)
  = match (|ty, e|) <: ty : ty_list & partial_eq_t ty with
  | (|[], Dl.DNil|)  -> p nil
  | (|t0 :: ts, Dl.DCons _ ox _ es|) ->
       let ox : option t0 = ox in
       match ox with
       | Some x -> forall_flist_part ts es (partial_app_flist_eq_Some t0 ts Type0 x es p)
       | None   -> (forall (x : t0) . forall_flist_part ts es (partial_app_flist_eq_None t0 ts Type0 x es p))

let rec exists_flist_part (ty : ty_list) (e : partial_eq_t ty) (p : (f : flist ty {partial_eq f e}) -> Type0)
  : Tot Type0 (decreases ty)
  = match (|ty, e|) <: ty : ty_list & partial_eq_t ty with
  | (|[], Dl.DNil|)  -> p nil
  | (|t0 :: ts, Dl.DCons _ ox _ es|) ->
       let ox : option t0 = ox in
       match ox with
       | Some x -> exists_flist_part ts es (partial_app_flist_eq_Some t0 ts Type0 x es p)
       | None   -> (exists (x : t0) . exists_flist_part ts es (partial_app_flist_eq_None t0 ts Type0 x es p))

#push-options "--ifuel 2 --fuel 2 --z3rlimit 10"
let rec forall_flist_part_iff (ty : ty_list) (e : partial_eq_t ty) (p : (f : flist ty {partial_eq f e}) -> Type0)
  : Lemma (ensures forall_flist_part ty e p <==> (forall (xs : flist ty {partial_eq xs e}) . p xs)) (decreases ty)
  = match (|ty, e|) <: ty : ty_list & partial_eq_t ty with
  | (|[], Dl.DNil|)  -> FStar.Classical.forall_intro nil_uniq
  | (|t0 :: ts, Dl.DCons _ ox _ es|) ->
       let ox : option t0 = ox in
       introduce forall (xs : flist ty {partial_eq xs e}) .
                   xs == cons (head #t0 #ts xs) (tail #t0 #ts xs) /\ partial_eq (tail #t0 #ts xs) es
         with as_cons #t0 #ts xs;
       match ox with
       | Some x ->
           calc (<==>) {
             forall (xs : flist ty {partial_eq xs e}) . p xs;
           <==> { }
             forall (xs' : flist ts {partial_eq xs' es}) . p (cons x xs');
           <==> { forall_flist_part_iff ts es (partial_app_flist_eq_Some t0 ts Type0 x es p) }
             forall_flist_part ty e p;
           }
       | None   ->
           calc (<==>) {
             forall (xs : flist ty {partial_eq xs e}) . p xs;
           <==> { }
             forall (x : t0) (xs' : flist ts {partial_eq xs' es}) . p (cons x xs');
           <==> {
               introduce forall (x : t0) .
                 forall_flist_part ts es (partial_app_flist_eq_None t0 ts Type0 x es p) <==>
                 (forall (xs : flist ts {partial_eq xs es}) . p (cons x xs))
               with forall_flist_part_iff ts es (partial_app_flist_eq_None t0 ts Type0 x es p)
              }
             forall (x : t0) . forall_flist_part ts es (partial_app_flist_eq_None t0 ts Type0 x es p);
           <==> { }
             forall_flist_part ty e p;
           }
#pop-options

#push-options "--ifuel 2 --fuel 2 --z3rlimit 30"
let rec exists_flist_part_iff (ty : ty_list) (e : partial_eq_t ty) (p : (f : flist ty {partial_eq f e}) -> Type0)
  : Lemma (ensures exists_flist_part ty e p <==> (exists (xs : flist ty {partial_eq xs e}) . p xs)) (decreases ty)
  = match (|ty, e|) <: ty : ty_list & partial_eq_t ty with
  | (|[], Dl.DNil|)  -> FStar.Classical.forall_intro nil_uniq
  | (|t0 :: ts, Dl.DCons _ ox _ es|) ->
       let ox : option t0 = ox in
       introduce forall (xs : flist ty {partial_eq xs e}) .
                   xs == cons (head #t0 #ts xs) (tail #t0 #ts xs) /\ partial_eq (tail #t0 #ts xs) es
         with as_cons #t0 #ts xs;
       match ox with
       | Some x ->
           calc (<==>) {
             exists (xs : flist ty {partial_eq xs e}) . p xs;
           <==> { }
             exists (xs' : flist ts {partial_eq xs' es}) . p (cons x xs');
           <==> { exists_flist_part_iff ts es (partial_app_flist_eq_Some t0 ts Type0 x es p) }
             exists_flist_part ty e p;
           }
       | None   ->
           calc (<==>) {
             exists (xs : flist ty {partial_eq xs e}) . p xs;
           <==> { }
             exists (x : t0) (xs' : flist ts {partial_eq xs' es}) . p (cons x xs');
           <==> {
               introduce forall (x : t0) .
                 exists_flist_part ts es (partial_app_flist_eq_None t0 ts Type0 x es p) <==>
                 (exists (xs : flist ts {partial_eq xs es}) . p (cons x xs))
               with exists_flist_part_iff ts es (partial_app_flist_eq_None t0 ts Type0 x es p)
              }
             exists (x : t0) . exists_flist_part ts es (partial_app_flist_eq_None t0 ts Type0 x es p);
           <==> { }
             exists_flist_part ty e p;
           }
#pop-options
