module Experiment.Steel.Repr.Fun

module U   = Learn.Util
module L   = FStar.List.Pure
module Ll  = Learn.List
module Fl  = Learn.FList
module Dl  = Learn.DList
module ST  = Experiment.Steel.Repr.ST
module Fin = FStar.Fin 

open Experiment.Steel.Repr.ST


type post_t (a : Type) = a -> Fl.ty_list
type post_v (#a : Type) (post : post_t a) (x : a) = Fl.flist (post x)
type req_t = prop
type ens_t (a : Type) (post : post_t a) = (x : a) -> post_v post x -> prop

noeq
type prog_tree : (a : Type u#a) -> (post : post_t u#a u#b a) -> Type u#(1 + max a b) =
  | Tspec : (a : Type u#a) -> (post : post_t a) ->
            (req : req_t) -> (ens : ens_t a post) ->
            prog_tree a post
  | Tret   : (a : Type u#a) -> (x : a) -> (post : post_t a) -> (sl : Dl.dlist (post x)) ->
             prog_tree a post
  | Tbind  : (a : Type u#a) -> (b : Type u#a) ->
             (itm : post_t a) -> (post : post_t b) ->
             (f : prog_tree a itm) -> (g : ((x : a) -> (sl : post_v itm x) -> prog_tree b post)) ->
             prog_tree b post
  | TbindP : (a : Type u#a) -> (b : Type u#a) ->
             (post : post_t b) ->
             (wp : pure_wp a) -> (x : unit -> PURE a wp) -> (g : a -> prog_tree b post) ->
             prog_tree b post

let rec tree_req (#a : Type) (#post : post_t a) (t : prog_tree a post)
  : Tot req_t (decreases t)
  = match t with
  | Tspec _ _  req _ ->
             req
  | Tret _ _ _ _ ->
             True
  | Tbind a _  itm _  f g ->
             tree_req f /\
               (forall (x : a) (sl : post_v itm x) . tree_ens f x sl ==> tree_req (g x sl))
  | TbindP a _  _  wp _ g ->
             wp (fun (x : a) -> tree_req (g x)) /\ True

and tree_ens (#a : Type) (#post : post_t a) (t : prog_tree a post)
  : Tot (ens_t a post) (decreases t)
  = match t with
  | Tspec _ _  _ ens ->
             ens
  | Tret _ x  post0 sl ->
             (fun x' (sl' : post_v post x') -> x' == x /\ sl' == Fl.flist_of_d sl)
  | Tbind a _  itm post0  f g ->
             (fun y (sl2 : post_v post y) ->
               (exists (x : a) (sl1 : post_v itm x) .
                 tree_ens f x sl1 /\ tree_ens (g x sl1) y sl2))
  | TbindP a _  post0  wp _ g ->
             (fun y (sl1 : post_v post y) ->
               (exists (x : a) . as_ensures wp x /\ tree_ens (g x) y sl1))


(*** Repr.ST --> Repr.Fun *)

module Opt = Learn.Option

//FIXME: necessary for push-options / pop-options to be interleaved correctly when checking the .fst
(**) val __begin_repr_fun_of_st : unit
#push-options "--fuel 1 --ifuel 1"

type post_src (pre_n : nat) (post_n : nat) = Fin.fin post_n -> option (Fin.fin pre_n)

let rec post_src_of_shape (#pre_n : nat) (#post_n : nat) (s : ST.shape_tree pre_n post_n)
  : Tot (post_src pre_n post_n) (decreases s)
  = match s with
  | Sequiv n p ->
           (fun i -> Some (p i))
  | Sframe pre_n post_n frame_n f ->
           (fun i -> if i < post_n
                  then Opt.map #(Fin.fin pre_n) #(Fin.fin (pre_n + frame_n)) (fun j -> j)
                               (post_src_of_shape f i)
                  else Some (i - post_n + pre_n))
  | Sspec  pre_n post_n ->
           (fun i -> None)
  | Sret   n ->
           (fun i -> None)
  | Sbind  pre_n itm_n post_n f g ->
            // bind returns all the selectors because with the current hypothesis, we need a value of the bound
            // type in order to prove that the propagated value (through g and f) has the correct type
           (fun i -> None)
  | SbindP pre_n post_n g ->
           (fun i -> None)

val post_src_ty
      (#a : Type) (#pre0 : ST.pre_t) (#post0 : ST.post_t a) (t : ST.prog_tree a pre0 post0)
      (s : ST.prog_shape t) (x : a) (i : Fin.fin (L.length (post0 x)))
  : Lemma (requires Some? (post_src_of_shape s.shp i))
          (ensures  L.index (post0 x) i == L.index pre0 (Some?.v (post_src_of_shape s.shp i)))

noeq
type post_bij_t' (#pre_n : nat) (#post_n : nat) (s : post_src pre_n post_n) = {
  post'_n : nat;
  post'_f : (i : Fin.fin post_n {None? (s i)}) -> Fin.fin post'_n;
  post'_g : Fin.fin post'_n -> (i : Fin.fin post_n  {None? (s i)});
}

type post_bij_t (#pre_n : nat) (#post_n : nat) (s : post_src pre_n post_n) =
  r : post_bij_t' s {
    (forall (i : Fin.fin post_n {None? (s i)}) . {:pattern (r.post'_g (r.post'_f i))}
      r.post'_g (r.post'_f i) = i) /\
    (forall (j : Fin.fin r.post'_n) . {:pattern (r.post'_f (r.post'_g j))}
      r.post'_f (r.post'_g j) = j)
  }

let rec mk_post_bij (#pre_n : nat) (#post_n : nat) (s : post_src pre_n post_n)
  : Tot (post_bij_t s) (decreases post_n)
  = if post_n = 0 then {
       post'_n = 0;
       post'_f = (fun _ -> false_elim ());
       post'_g = (fun _ -> false_elim ())}
    else
      let s' : post_src pre_n (post_n - 1) = fun i -> s (i+1) in
      let p' = mk_post_bij s' in
      match s 0 with
      | Some _ -> { post'_n = p'.post'_n;
                   post'_f = (fun i -> p'.post'_f (i-1));
                   post'_g = (fun j -> p'.post'_g j + 1)}
      | None   -> { post'_n = p'.post'_n + 1;
                   post'_f = (fun i -> if i = 0 then 0 else (p'.post'_f (i-1) + 1));
                   post'_g = (fun j -> if j = 0 then 0 else (p'.post'_g (j-1) + 1))}

let rec post_bij (#post_n : nat) (#pre_n : nat) (s : ST.shape_tree pre_n post_n)
  : Tot (post_bij_t (post_src_of_shape s)) (decreases s)
  = match s with
  | Sequiv n p ->
           { post'_n = 0; post'_f = (fun _ -> false_elim ()); post'_g = (fun _ -> false_elim ()) }
  | Sframe pre_n post_n frame_n f ->
           let bj = post_bij f in
           { post'_n = bj.post'_n;
             post'_f = (fun (i : Fin.fin (post_n + frame_n) {None? (post_src_of_shape s i)}) -> bj.post'_f i);
             post'_g = bj.post'_g }
  | Sspec  pre_n post_n ->
           { post'_n = post_n; post'_f = (fun i -> i); post'_g = (fun j -> j) }
  | Sret   n ->
           { post'_n = n; post'_f = (fun i -> i); post'_g = (fun j -> j) }
  | Sbind  pre_n itm_n post_n f g ->
           { post'_n = post_n; post'_f = (fun i -> i); post'_g = (fun j -> j) }
  | SbindP pre_n post_n g ->
           { post'_n = post_n; post'_f = (fun i -> i); post'_g = (fun j -> j) }


let post_Fun_of_ST
      (#a : Type u#a) (post : ST.post_t u#a u#b a)
      (#pre_n #post_n : nat) (s : ST.shape_tree pre_n post_n {post_has_len post post_n})
  : post_t u#a u#b a
  = let p' = post_bij s in
    fun (x : a) -> Ll.initi 0 p'.post'_n (fun i -> L.index (post x) (p'.post'_g i))

// TODO? define with post : ty_list
let sel_Fun_of_ST
      (#a : Type u#a) (post : ST.post_t u#a u#b a)
      (#pre_n #post_n : nat) (s : ST.shape_tree pre_n post_n {post_has_len post post_n})
      (x : a) (post_val : Fl.flist (post x))
  : post_v (post_Fun_of_ST post s) x
  = let p' = post_bij s in
    Fl.mk_flist (post_Fun_of_ST post s x)
                (fun i -> U.cast (L.index (post_Fun_of_ST post s x) i) (post_val (p'.post'_g i)))

unfold
let return_Fun_post'_of_ST
      (#a : Type u#a) (post : ST.post_t u#a u#b a)
      (#pre_n #post_n : nat) (s : ST.shape_tree pre_n post_n {post_has_len post post_n})
      (x : a) (post_val : Fl.flist (post x))
  : prog_tree a (post_Fun_of_ST post s)
  = Tret a x (post_Fun_of_ST post s) (Fl.dlist_of_f (sel_Fun_of_ST post s x post_val))

// TODO? remove the dependency in [t]
let sel_ST_of_Fun
      (#a : Type) (#pre : ST.pre_t) (#post : ST.post_t a) (t : ST.prog_tree a pre post)
      (s : ST.prog_shape t)
      (sl0 : Fl.flist pre) (x : a) (sl1' : post_v (post_Fun_of_ST post s.shp) x)
  : Fl.flist (post x)
  =
    let p' = post_bij s.shp in
    Fl.mk_flist (post x)
             (fun i -> match post_src_of_shape s.shp i with
                    | Some j -> (**) post_src_ty t s x i;
                               U.cast (L.index (post x) i)
                                      (sl0 j)
                    | None   -> U.cast (L.index (post x) i)
                                      (sl1' (p'.post'_f i)))

val sel_Fun_ST_Fun
      (#a : Type) (#pre : ST.pre_t) (#post : ST.post_t a) (t : ST.prog_tree a pre post)
      (s : ST.prog_shape t)
      (sl0 : Fl.flist pre) (x : a) (sl1' : post_v (post_Fun_of_ST post s.shp) x)
  : Lemma (sel_Fun_of_ST post s.shp x (sel_ST_of_Fun t s sl0 x sl1') == sl1')


val post_Fun_of_ST__frame
      (#a : Type) (post : ST.post_t a) (frame: Fl.ty_list)
      (pre_n : nat) (post_n : nat {post_has_len post post_n}) (f : shape_tree pre_n post_n)
  : Lemma (post_Fun_of_ST (ST.frame_post post frame) (Sframe pre_n post_n (L.length frame) f)
                == post_Fun_of_ST post f)

val post_Fun_of_ST__spec
      (#a : Type) (post : ST.post_t a)
      (pre_n : nat) (post_n : nat {post_has_len post post_n})
  : Lemma (post_Fun_of_ST post (Sspec pre_n post_n) == U.eta post)

val post_Fun_of_ST__ret
      (#a : Type) (post : ST.post_t a) (post_n : nat {post_has_len post post_n})
  : Lemma (post_Fun_of_ST post (Sret post_n) == U.eta post)


(* TODO? markers *)
let rec repr_Fun_of_ST
          (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
          (t : ST.prog_tree a pre post)
  : Tot ((s : ST.prog_shape t) -> Fl.flist pre -> prog_tree a (post_Fun_of_ST post s.shp))
        (decreases t)
  = match t as t'
      returns (s : ST.prog_shape t) -> Fl.flist pre ->
              prog_tree a (post_Fun_of_ST post s.shp)
    with
    | ST.Tequiv pre post0 p -> fun s sl0 ->
            Tret U.unit' U.Unit' (fun _ -> []) Dl.DNil
    | ST.Tframe a pre post frame f -> fun s sl0 ->
            (**) let Sframe _ post_n _ shp_f = s.shp in
            (**) post_Fun_of_ST__frame post frame (L.length pre) post_n shp_f;
            let sl0' : Fl.flist pre = (Fl.splitAt_ty pre frame sl0)._1 in
            repr_Fun_of_ST f (ST.mk_prog_shape f shp_f) sl0'
    | ST.Tspec a pre post req ens -> fun s sl0 ->
            (**) let Sspec _ post_n = s.shp in
            (**) post_Fun_of_ST__spec post (L.length pre) post_n;
            Tspec a (U.eta post) (req sl0) (ens sl0)
    | ST.Tret a x post -> fun s sl ->
            (**) let Sret post_n = s.shp in
            (**) post_Fun_of_ST__ret post post_n;
            Tret a x (U.eta post) (Fl.dlist_of_f sl)
    | ST.Tbind a b pre itm post f g -> fun s sl0 ->
            (**) let Sbind _ itm_n post_n shp_f shp_g = s.shp in
            (**) let s_f = ST.mk_prog_shape f shp_f in
            Tbind a b  _ _ (repr_Fun_of_ST f s_f sl0) (fun x sl1' ->
            (**) let s_g : prog_shape (g x) = ST.mk_prog_shape (g x) shp_g in
            let sl1 = sel_ST_of_Fun f s_f sl0 x sl1' in
            Tbind b b  (post_Fun_of_ST post #(L.length (itm x)) shp_g) _
                       (repr_Fun_of_ST (g x) s_g sl1) (fun y sl2' ->
            let sl2 = sel_ST_of_Fun (g x) s_g sl1 y sl2' in
            return_Fun_post'_of_ST post s.shp y sl2))
    | ST.TbindP a b pre post wp f g -> fun s sl0 ->
            (**) let SbindP _ post_n shp_g = s.shp in
            TbindP a b _ wp f (fun x ->
            (**) let s_g : prog_shape (g x) = ST.mk_prog_shape (g x) shp_g in
            Tbind  b b (post_Fun_of_ST post #(L.length #Type pre) shp_g) _
                       (repr_Fun_of_ST (g x) s_g sl0) (fun y sl1' ->
            let sl1 = sel_ST_of_Fun (g x) s_g sl0 y sl1' in
            return_Fun_post'_of_ST post s.shp y sl1))

(**) val __end_repr_fun_of_st : unit
#pop-options


(***** soundness of ST --> Fun *)

let post_eq_src (#pre #post : Fl.ty_list) (sl0 : Fl.flist pre) (sl1 : Fl.flist post)
                (s : post_src (L.length pre) (L.length post))
  : prop
  = forall (i : Fin.fin (L.length post)) .
      Some? (s i) ==> sl1 i === sl0 (Some?.v (s i))

val sel_ST_of_Fun_eq_src
      (#a : Type) (#pre : ST.pre_t) (#post : ST.post_t a)
      (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre) (x : a) (sl1' : post_v (post_Fun_of_ST post s.shp) x)
  : Lemma (post_eq_src sl0 (sel_ST_of_Fun t s sl0 x sl1') (post_src_of_shape s.shp))

val post_eq_src_ST_Fun_ST
      (#a : Type) (#pre : ST.pre_t) (#post : ST.post_t a)
      (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre) (x : a) (sl1 : Fl.flist (post x))
  : Lemma (requires post_eq_src sl0 sl1 (post_src_of_shape s.shp))
          (ensures  sel_ST_of_Fun t s sl0 x (sel_Fun_of_ST post s.shp x sl1) == sl1)

(* TODO? def de post_eq_src *)
let post_eq_src_iff
      #a #pre #post (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre) (x : a) (sl1 : Fl.flist (post x))
  : Lemma (post_eq_src sl0 sl1 (post_src_of_shape s.shp)
           <==> sl1 == sel_ST_of_Fun t s sl0 x (sel_Fun_of_ST post s.shp x sl1))
  = sel_ST_of_Fun_eq_src t s sl0 x (sel_Fun_of_ST post s.shp x sl1);
    FStar.Classical.move_requires (post_eq_src_ST_Fun_ST t s sl0 x) sl1


unfold
let req_equiv #a #pre #post (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre)
  : prop
  = ST.tree_req t sl0 <==> tree_req (repr_Fun_of_ST t s sl0)

unfold
let ens_equiv #a #pre #post (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre) (res : a) (sl1 : Fl.flist (post res))
  : prop
  = ST.tree_ens t sl0 res sl1 <==>
   (post_eq_src sl0 sl1 (post_src_of_shape s.shp) /\
    tree_ens (repr_Fun_of_ST t s sl0) res (sel_Fun_of_ST post s.shp res sl1))

let ens_equiv_rev #a #pre #post (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre) (res : a) (sl1' : post_v (post_Fun_of_ST post s.shp) res)
  : Lemma (requires ens_equiv t s sl0 res (sel_ST_of_Fun t s sl0 res sl1'))
          (ensures  ST.tree_ens t sl0 res (sel_ST_of_Fun t s sl0 res sl1') <==>
                    tree_ens (repr_Fun_of_ST t s sl0) res sl1')
  =
    sel_ST_of_Fun_eq_src t s sl0 res sl1';
    sel_Fun_ST_Fun t s sl0 res sl1'


/// The soundness (and completeness) lemmas:

val repr_Fun_of_ST_req
  (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
  (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
  (sl0 : Fl.flist pre)
  : Lemma (req_equiv t s sl0)

val repr_Fun_of_ST_ens
  (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
  (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
  (sl0 : Fl.flist pre) (res : a) (sl1 : Fl.flist (post res))
  : Lemma (ens_equiv t s sl0 res sl1)


(*** Steel.Repr.Fun --> Repr.Fun *)

(**) val __begin_repr_fun_of_steel : unit

module Fun = Experiment.Repr.Fun

noeq
type sl_tys_t : Type u#(max a b + 1)= {
  val_t : Type u#a;
  sel_t : post_t u#a u#b val_t
}

noeq
type sl_tys_v (ty : sl_tys_t u#a u#b) : Type u#(max a (b + 1)) = {
  val_v : ty.val_t;
  sel_v : Fl.flist (ty.sel_t val_v)
}

let sl_all (ty : sl_tys_t) (f : sl_tys_v ty -> Type0)
  : Type0
  =
   (forall (val_v : ty.val_t) . Fl.forall_flist (ty.sel_t val_v) (fun sel_v -> f ({val_v; sel_v})))


let sl_all_iff (ty : sl_tys_t) (f : sl_tys_v ty -> Type0)
  : Lemma (sl_all ty f  <==> (forall (x : sl_tys_v ty) . f x))
          [SMTPat (sl_all ty f)]
  =
    assert (forall (x : sl_tys_v ty) . x == {val_v = x.val_v; sel_v = x.sel_v})

let sl_ex (ty : sl_tys_t) (f : sl_tys_v ty -> Type0)
  : Type0
  =
   (exists (val_v : ty.val_t) . Fl.exists_flist (ty.sel_t val_v) (fun sel_v -> f ({val_v; sel_v})))

let sl_ex_iff (ty : sl_tys_t) (f : sl_tys_v ty -> Type0)
  : Lemma (sl_ex ty f  <==> (exists (x : sl_tys_v ty) . f x))
          [SMTPat (sl_ex ty f)]
  =
    assert (forall (x : sl_tys_v ty) . x == {val_v = x.val_v; sel_v = x.sel_v})


let sl_arw (src : sl_tys_t u#a u#b) (dst : Type u#d) : Type =
  (x : src.val_t) -> Fl.arw_list (src.sel_t x) dst

let sl_lam (src : sl_tys_t u#a u#b) (dst : Type u#d) (f : (x : src.val_t) -> (xs : Fl.flist (src.sel_t x)) -> dst)
  : sl_arw src dst
  = fun (x : src.val_t) -> Fl.lam_flist (src.sel_t x) dst (f x)

let sl_app (#src : sl_tys_t u#a u#b) (#dst : Type u#d) (f : sl_arw src dst) (x : sl_tys_v src) : dst
  = Fl.app_flist (f x.val_v) x.sel_v

let sl_app_lam (src : sl_tys_t u#a u#b) (dst : Type u#d)
               (f : (x : src.val_t) -> (xs : Fl.flist (src.sel_t x)) -> dst) (x : sl_tys_v src)
  : Lemma (ensures sl_app (sl_lam src dst f) x == f x.val_v x.sel_v)
          [SMTPat (sl_app (sl_lam src dst f) x)]
  = ()

unfold
let sl_uncurrify (#val_t : Type) (#sel_t : post_t val_t) (#dst : Type)
                 (f : (v : val_t) -> (sls : Fl.flist (sel_t v)) -> dst)
                 (x : sl_tys_v ({val_t; sel_t})) : dst
  = f x.val_v x.sel_v

unfold
let sl_tys' : Fun.tys' u#(max a b + 1) u#(max a (b + 1)) = {
  t = sl_tys_t u#a u#b;
  v = sl_tys_v u#a u#b;
  unit = {val_t = U.unit'; sel_t = (fun _ -> [])};
  emp  = {val_v = U.Unit'; sel_v = Fl.nil};
  all  = sl_all;
  ex   = sl_ex;
}

let sl_tys : Fun.tys u#(max a b + 1) u#(max a (b + 1)) =
  (**) introduce forall (x : sl_tys'.v sl_tys'.unit) . x == sl_tys'.emp
  (**)   with Fl.nil_uniq x.sel_v;
  sl_tys'


let rec repr_Fun_of_Steel (#val_t : Type u#a) (#sel_t : post_t u#a u#b val_t) (t : prog_tree val_t sel_t)
  : Tot (Fun.prog_tree u#(max a b + 1) u#(max a (b + 1)) u#a (sl_tys u#a u#b) ({val_t; sel_t}))
        (decreases t)
  = match t with
  | Tspec a post req ens ->
          Fun.Tspec ({val_t = a; sel_t = post}) req (sl_uncurrify ens)
  | Tret a x post sl ->
          Fun.Tret #sl_tys ({val_t = a; sel_t = post}) ({val_v = x; sel_v = Fl.flist_of_d sl})
  | Tbind a b itm post f g ->
          Fun.Tbind _ _ (repr_Fun_of_Steel f) (sl_uncurrify (fun x sls -> repr_Fun_of_Steel (g x sls)))
  | TbindP a b post wp f g ->
           Fun.TbindP a ({val_t = b; sel_t = post}) wp f (fun (x : a) -> repr_Fun_of_Steel (g x))


(***** soundness of Steel.Fun --> Fun *)

val repr_Fun_of_Steel_req (#val_t : Type) (#sel_t : post_t val_t) (t : prog_tree u#a u#b val_t sel_t)
  : Lemma (tree_req t <==> Fun.tree_req (repr_Fun_of_Steel t))

val repr_Fun_of_Steel_ens (#val_t : Type) (#sel_t : post_t val_t) (t : prog_tree u#a u#b val_t sel_t)
                          (val_v : val_t) (sel_v : Fl.flist (sel_t val_v))
  : Lemma (tree_ens t val_v sel_v <==> Fun.tree_ens (repr_Fun_of_Steel t) ({val_v; sel_v}))
