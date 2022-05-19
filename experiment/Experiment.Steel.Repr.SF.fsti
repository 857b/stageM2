module Experiment.Steel.Repr.SF

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
type req_t = Type0
type ens_t (a : Type) (post : post_t a) = (x : a) -> post_v post x -> Type0

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
             wp (fun (x : a) -> tree_req (g x))

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


(***** Shape *)

type shape_tree : (post_n : nat) -> Type =
  | Sspec  : (post_n : nat) ->
             shape_tree post_n
  | Sret   : (smp_ret : bool) -> (n : nat) ->
             shape_tree n
  | Sbind  : (itm_n : nat) -> (post_n : nat) ->
             (f : shape_tree itm_n) -> (g : shape_tree post_n) ->
             shape_tree post_n
  | SbindP : (post_n : nat) ->
             (g : shape_tree post_n) ->
             shape_tree post_n

let rec prog_has_shape (#a : Type u#a) (#post : post_t u#a u#b a)
                       (t : prog_tree a post)
                       (#post_n : nat) (s : shape_tree post_n)
  : Pure prop (requires True)
              (ensures fun p -> p ==> post_has_len post post_n)
              (decreases t)
  =
    post_has_len post post_n /\
    (match t returns prop with
    | Tspec  _ post _ _       -> s == Sspec post_n
    | Tret   _ _ _ _          -> exists (smp_ret : bool) .
                                s == Sret   smp_ret _
    | Tbind  a b itm post f g -> exists (itm_n : nat)
                                  (s_f : shape_tree itm_n)
                                  (s_g : shape_tree post_n) .
                                s == Sbind _ _ s_f s_g /\
                                prog_has_shape f s_f /\
                                (forall (x : a) (sl1 : post_v itm x) . prog_has_shape (g x sl1) s_g)
    | TbindP a _ post _ _ g   -> exists (s_g : shape_tree post_n) .
                                s == SbindP _ s_g /\
                               (forall (x : a) . prog_has_shape (g x) s_g)
    )

noeq
type prog_shape (#a : Type) (#post : post_t a) (t : prog_tree a post) = {
  post_len : (l : nat {post_has_len post l});
  shp      : (s : shape_tree post_len {prog_has_shape t s});
}

unfold
let mk_prog_shape (#a : Type) (#post : post_t a) (t : prog_tree a post)
                  (#post_len : nat) (shp : shape_tree post_len {prog_has_shape t shp})
  : prog_shape t =
  { post_len; shp}


(*** Repr.ST --> Repr.SF *)

module Opt = Learn.Option

//FIXME: necessary for push-options / pop-options to be interleaved correctly when checking the .fst
(**) val __begin_repr_fun_of_st : unit
#push-options "--fuel 1 --ifuel 1"

type post_src_f (pre_n : nat) (post_n : nat) = Fin.fin post_n -> option (Fin.fin pre_n)

let rec post_src_f_of_shape (#pre_n : nat) (#post_n : nat) (s : ST.shape_tree pre_n post_n)
  : Tot (post_src_f pre_n post_n) (decreases s)
  = match s with
  | ST.Sequiv n p ->
           (fun i -> Some (p i))
  | ST.Sframe pre_n post_n frame_n f ->
           (fun i -> if i < post_n
                  then Opt.map #(Fin.fin pre_n) #(Fin.fin (pre_n + frame_n)) (fun j -> j)
                               (post_src_f_of_shape f i)
                  else Some (i - post_n + pre_n))
  | ST.Sspec  pre_n post_n ->
           (fun i -> None)
  | ST.Sret   _ n ->
           (fun i -> None)
  | ST.Sbind  pre_n itm_n post_n f g ->
            // bind returns all the selectors because with the current hypothesis, we need a value of the bound
            // type in order to prove that the propagated value (through g and f) has the correct type
           (fun i -> None)
  | ST.SbindP pre_n post_n g ->
           (fun i -> None)


let post_src_well_typed (pre post : Fl.ty_list) (f : post_src_f (L.length pre) (L.length post)) : prop
  = forall (i : Fin.fin (L.length post) {Some? (f i)}) . {:pattern (f i)}
      L.index post i == L.index pre (Some?.v (f i))

type post_src (pre post : Fl.ty_list) =
  f : post_src_f (L.length pre) (L.length post) {post_src_well_typed pre post f}

let post_src_ty_eq (#pre #post : Fl.ty_list) (f : post_src_f (L.length pre) (L.length post))
                   (i : Fin.fin (L.length post))
  : Lemma (requires post_src_well_typed pre post f /\ Some? (f i))
          (ensures  L.index post i == L.index pre (Some?.v (f i)))
  = ()

val post_src_of_shape_ty
      (#a : Type) (#pre : ST.pre_t) (#post : ST.post_t a) (t : ST.prog_tree a pre post)
      (s : ST.prog_shape t) (x : a) (i : Fin.fin (L.length (post x)) {Some? (post_src_f_of_shape s.shp i)})
  : Lemma (L.index (post x) i == L.index pre (Some?.v (post_src_f_of_shape s.shp i)))

unfold
let post_src_of_shape
      (#a : Type) (#pre : ST.pre_t) (#post : ST.post_t a) (t : ST.prog_tree a pre post)
      (s : ST.prog_shape t) (x : a)
  : post_src pre (post x)
  =
    (**) FStar.Classical.forall_intro (post_src_of_shape_ty t s x);
    post_src_f_of_shape s.shp

noeq
type post_bij_t' (#pre_n : nat) (#post_n : nat) (s : post_src_f pre_n post_n) = {
  len_SF : nat;
  idx_SF : (i : Fin.fin post_n {None? (s i)}) -> Fin.fin len_SF;
  idx_ST  : Fin.fin len_SF -> (i : Fin.fin post_n  {None? (s i)});
}

type post_bij_t (#pre_n : nat) (#post_n : nat) (s : post_src_f pre_n post_n) =
  r : post_bij_t' s {
    (forall (i : Fin.fin post_n {None? (s i)}) . {:pattern (r.idx_ST (r.idx_SF i))}
      r.idx_ST (r.idx_SF i) = i) /\
    (forall (j : Fin.fin r.len_SF) . {:pattern (r.idx_SF (r.idx_ST j))}
      r.idx_SF (r.idx_ST j) = j)
  }

let rec mk_post_bij (#pre_n : nat) (#post_n : nat) (s : post_src_f pre_n post_n)
  : Tot (post_bij_t s) (decreases post_n)
  = if post_n = 0 then {
       len_SF = 0;
       idx_SF = (fun _ -> false_elim ());
       idx_ST  = (fun _ -> false_elim ())}
    else
      let s' : post_src_f pre_n (post_n - 1) = fun i -> s (i+1) in
      let p' = mk_post_bij s' in
      match s 0 with
      | Some _ -> { len_SF = p'.len_SF;
                   idx_SF = (fun i -> p'.idx_SF (i-1));
                   idx_ST = (fun j -> p'.idx_ST j + 1)}
      | None   -> { len_SF = p'.len_SF + 1;
                   idx_SF = (fun i -> if i = 0 then 0 else (p'.idx_SF (i-1) + 1));
                   idx_ST = (fun j -> if j = 0 then 0 else (p'.idx_ST (j-1) + 1))}

let rec post_bij (#post_n : nat) (#pre_n : nat) (s : ST.shape_tree pre_n post_n)
  : Tot (post_bij_t (post_src_f_of_shape s)) (decreases s)
  = match s with
  | ST.Sequiv n p ->
           { len_SF = 0; idx_SF = (fun _ -> false_elim ()); idx_ST = (fun _ -> false_elim ()) }
  | ST.Sframe pre_n post_n frame_n f ->
           let bj = post_bij f in
           { len_SF = bj.len_SF;
             idx_SF = (fun (i : Fin.fin (post_n + frame_n) {None? (post_src_f_of_shape s i)}) -> bj.idx_SF i);
             idx_ST = bj.idx_ST }
  | ST.Sspec  pre_n post_n ->
           { len_SF = post_n; idx_SF = (fun i -> i); idx_ST = (fun j -> j) }
  | ST.Sret   _ n ->
           { len_SF = n; idx_SF = (fun i -> i); idx_ST = (fun j -> j) }
  | ST.Sbind  pre_n itm_n post_n f g ->
           { len_SF = post_n; idx_SF = (fun i -> i); idx_ST = (fun j -> j) }
  | ST.SbindP pre_n post_n g ->
           { len_SF = post_n; idx_SF = (fun i -> i); idx_ST = (fun j -> j) }


let postl_SF_of_ST
      (post : Fl.ty_list)
      (#pre_n : nat) (#s : post_src_f pre_n (L.length post)) (bij : post_bij_t s)
  : Fl.ty_list
  = Ll.initi 0 bij.len_SF (fun i -> L.index post (bij.idx_ST i))

let post_SF_of_ST
      (#a : Type u#a) (post : ST.post_t u#a u#b a)
      (#pre_n #post_n : nat) (s : ST.shape_tree pre_n post_n {post_has_len post post_n})
  : post_t u#a u#b a
  = fun (x : a) -> postl_SF_of_ST (post x) (post_bij s)

let sell_SF_of_ST
      (post : Fl.ty_list)
      (#pre_n : nat) (#s : post_src_f pre_n (L.length post)) (bij : post_bij_t s)
      (sl_ST : Fl.flist post)
  : Fl.flist (postl_SF_of_ST post bij)
  = 
    Fl.mk_flist (postl_SF_of_ST post bij)
                (fun i -> U.cast (L.index (postl_SF_of_ST post bij) i) (sl_ST (bij.idx_ST i)))

let sel_SF_of_ST
      (#a : Type u#a) (post : ST.post_t u#a u#b a)
      (#pre_n #post_n : nat) (s : ST.shape_tree pre_n post_n {post_has_len post post_n})
      (x : a)
  : Fl.flist (post x) -> post_v (post_SF_of_ST post s) x
  = sell_SF_of_ST (post x) (post_bij s)

unfold
let return_SF_post_of_ST
      (#a : Type u#a) (post : ST.post_t u#a u#b a)
      (#pre_n #post_n : nat) (s : ST.shape_tree pre_n post_n {post_has_len post post_n})
      (x : a) (post_val : Fl.flist (post x))
  : prog_tree a (post_SF_of_ST post s)
  = Tret a x (post_SF_of_ST post s) (Fl.dlist_of_f (sel_SF_of_ST post s x post_val))


let sell_ST_of_SF
      (#pre #post : Fl.ty_list)
      (s : post_src pre post) (bij : post_bij_t s)
      (sl0 : Fl.flist pre) (sl1_SF : Fl.flist (postl_SF_of_ST post bij))
  : Fl.flist post
  =
    Fl.mk_flist post
         (fun i -> match s i with
                | Some j -> U.cast (L.index post i) (sl0 j)
                | None   -> U.cast (L.index post i) (sl1_SF (bij.idx_SF i)))

let sel_ST_of_SF
      (#a : Type) (#pre : ST.pre_t) (#post : ST.post_t a) (t : ST.prog_tree a pre post)
      (s : ST.prog_shape t)
      (sl0 : Fl.flist pre) (x : a) (sl1_SF : post_v (post_SF_of_ST post s.shp) x)
  : Fl.flist (post x)
  = sell_ST_of_SF (post_src_of_shape t s x) (post_bij s.shp) sl0 sl1_SF

val sell_SF_ST_SF
      (#pre #post : Fl.ty_list)
      (s : post_src pre post) (bij : post_bij_t s)
      (sl0 : Fl.flist pre) (sl1_SF : Fl.flist (postl_SF_of_ST post bij))
  : Lemma (sell_SF_of_ST post bij (sell_ST_of_SF s bij sl0 sl1_SF) == sl1_SF)

let sel_SF_ST_SF
      (#a : Type) (#pre : ST.pre_t) (#post : ST.post_t a) (t : ST.prog_tree a pre post)
      (s : ST.prog_shape t)
      (sl0 : Fl.flist pre) (x : a) (sl1_SF : post_v (post_SF_of_ST post s.shp) x)
  : Lemma (sel_SF_of_ST post s.shp x (sel_ST_of_SF t s sl0 x sl1_SF) == sl1_SF)
  = sell_SF_ST_SF (post_src_of_shape t s x) (post_bij s.shp) sl0 sl1_SF


val post_SF_of_ST__frame
      (#a : Type) (post : ST.post_t a) (frame: Fl.ty_list)
      (pre_n : nat) (post_n : nat {post_has_len post post_n}) (f : ST.shape_tree pre_n post_n)
  : Lemma (post_SF_of_ST (ST.frame_post post frame) (Sframe pre_n post_n (L.length frame) f)
                == post_SF_of_ST post f)

val post_SF_of_ST__spec
      (#a : Type) (post : ST.post_t a)
      (pre_n : nat) (post_n : nat {post_has_len post post_n})
  : Lemma (post_SF_of_ST post (ST.Sspec pre_n post_n) == U.eta post)

val post_SF_of_ST__ret
      (#a : Type) (post : ST.post_t a) (smp_ret : bool) (post_n : nat {post_has_len post post_n})
  : Lemma (post_SF_of_ST post (ST.Sret smp_ret post_n) == U.eta post)


let rec repr_SF_of_ST
      (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
      (t : ST.prog_tree a pre post)
  : Tot ((s : ST.prog_shape t) -> Fl.flist pre -> prog_tree a (post_SF_of_ST post s.shp))
        (decreases t)
  = match t as t'
      returns (s : ST.prog_shape t) -> Fl.flist pre ->
              prog_tree a (post_SF_of_ST post s.shp)
    with
    | ST.Tequiv pre post0 p -> fun s sl0 ->
            Tret U.unit' U.Unit' (fun _ -> []) Dl.DNil
    | ST.Tframe a pre post frame f -> fun s sl0 ->
            (**) let ST.Sframe _ post_n _ shp_f = s.shp in
            (**) post_SF_of_ST__frame post frame (L.length pre) post_n shp_f;
            let sl0' : Fl.flist pre = (Fl.splitAt_ty pre frame sl0)._1 in
            repr_SF_of_ST f (ST.mk_prog_shape f shp_f) sl0'
    | ST.Tspec a pre post req ens -> fun s sl0 ->
            (**) let ST.Sspec _ post_n = s.shp in
            (**) post_SF_of_ST__spec post (L.length pre) post_n;
            Tspec a (U.eta post) (req sl0) (ens sl0)
    | ST.Tret a x post -> fun s sl ->
            (**) let ST.Sret smp_ret post_n = s.shp in
            (**) post_SF_of_ST__ret post smp_ret post_n;
            Tret a x (U.eta post) (Fl.dlist_of_f sl)
    | ST.Tbind a b pre itm post f g -> fun s sl0 ->
            (**) let ST.Sbind _ itm_n post_n shp_f shp_g = s.shp in
            (**) let s_f = ST.mk_prog_shape f shp_f in
            Tbind a b  _ _ (repr_SF_of_ST f s_f sl0) (fun x sl1' ->
            (**) let s_g : ST.prog_shape (g x) = ST.mk_prog_shape (g x) shp_g in
            let sl1 = sel_ST_of_SF f s_f sl0 x sl1' in
            Tbind b b  (post_SF_of_ST post #(L.length (itm x)) shp_g) _
                       (repr_SF_of_ST (g x) s_g sl1) (fun y sl2' ->
            let sl2 = sel_ST_of_SF (g x) s_g sl1 y sl2' in
            return_SF_post_of_ST post s.shp y sl2))
    | ST.TbindP a b pre post wp f g -> fun s sl0 ->
            (**) let ST.SbindP _ post_n shp_g = s.shp in
            TbindP a b _ wp f (fun x ->
            (**) let s_g : ST.prog_shape (g x) = ST.mk_prog_shape (g x) shp_g in
            Tbind  b b (post_SF_of_ST post #(L.length #Type pre) shp_g) _
                       (repr_SF_of_ST (g x) s_g sl0) (fun y sl1' ->
            let sl1 = sel_ST_of_SF (g x) s_g sl0 y sl1' in
            return_SF_post_of_ST post s.shp y sl1))

/// A version that returns all selectors, to be used at top-level
let repr_SF_of_ST_rall
      (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
      (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre)
  : prog_tree a post
  = Tbind a a _ _ (repr_SF_of_ST t s sl0) (fun x sl1' ->
    let sl1 = sel_ST_of_SF t s sl0 x sl1' in
    Tret a x post (Fl.dlist_of_f sl1))


let rec shape_SF_of_ST
      (#pre_n #post_n : nat) (t : ST.shape_tree pre_n post_n)
  : Tot (shape_tree (post_bij t).len_SF) (decreases t)
  = match t with
    | ST.Sequiv _ _ ->
            Sret true 0
    | ST.Sframe pre_n post_n frame_n s_f ->
            shape_SF_of_ST s_f
    | ST.Sspec pre_n post_n ->
            Sspec post_n
    | ST.Sret smp_ret n ->
            Sret smp_ret n
    | ST.Sbind pre_n itm_n post_n s_f s_g ->
            Sbind _ _ (shape_SF_of_ST s_f) (
            Sbind _ _ (shape_SF_of_ST s_g)
                      (Sret true post_n))
    | ST.SbindP pre_n post_n s_g ->
            SbindP _ (Sbind _ _ (shape_SF_of_ST s_g) (Sret true post_n))

let shape_SF_of_ST_rall
      (#pre_n #post_n : nat) (t : ST.shape_tree pre_n post_n)
  : shape_tree post_n
  = Sbind (post_bij t).len_SF post_n
       (shape_SF_of_ST t) (Sret true post_n)

(**) val __end_repr_fun_of_st : unit
#pop-options


(***** soundness of ST --> SF *)

// TODO? pattern
let post_eq_src (#pre #post : Fl.ty_list) (s : post_src pre post)
                (sl0 : Fl.flist pre) (sl1_ST : Fl.flist post)
  : prop
  = forall (i : Fin.fin (L.length post) {Some? (s i)}) .
      sl1_ST i == U.cast (L.index post i) (sl0 (Some?.v (s i)))

let post_eq_srcD
      (#pre #post : Fl.ty_list) (s : post_src pre post)
      (sl0 : Fl.flist pre) (sl1_ST : Fl.flist post)
      (i : Fin.fin (L.length post))
  : Lemma (requires post_eq_src s sl0 sl1_ST /\ Some? (s i))
          (ensures  sl1_ST i === sl0 (Some?.v (s i)))
  = eliminate forall (i : Fin.fin (L.length post) {Some? (s i)}) .
                sl1_ST i == U.cast (L.index post i) (sl0 (Some?.v (s i)))
      with i

val sell_ST_of_SF_eq_src
      (#pre #post : Fl.ty_list)
      (s : post_src pre post) (bij : post_bij_t s)
      (sl0 : Fl.flist pre) (sl1_SF : Fl.flist (postl_SF_of_ST post bij))
  : Lemma (post_eq_src s sl0 (sell_ST_of_SF s bij sl0 sl1_SF))

val post_eq_src_ST_SF_ST
      (#pre #post : Fl.ty_list)
      (s : post_src pre post) (bij : post_bij_t s)
      (sl0 : Fl.flist pre) (sl1_ST : Fl.flist post)
  : Lemma (requires post_eq_src s sl0 sl1_ST)
          (ensures  sell_ST_of_SF s bij sl0 (sell_SF_of_ST post bij sl1_ST) == sl1_ST)

(* TODO? def de post_eq_src *)
let post_eq_src_iff
      (#pre #post : Fl.ty_list) (s : post_src pre post) (bij : post_bij_t s)
      (sl0 : Fl.flist pre) (sl1_ST : Fl.flist post)
  : Lemma (post_eq_src s sl0 sl1_ST
           <==> sl1_ST == sell_ST_of_SF s bij sl0 (sell_SF_of_ST post bij sl1_ST))
  = sell_ST_of_SF_eq_src s bij sl0 (sell_SF_of_ST post bij sl1_ST);
    FStar.Classical.move_requires (post_eq_src_ST_SF_ST s bij sl0) sl1_ST


unfold
let req_equiv #a #pre #post (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre)
  : prop
  = ST.tree_req t sl0 <==> tree_req (repr_SF_of_ST t s sl0)

unfold
let ens_equiv #a #pre #post (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre) (res : a) (sl1_ST : Fl.flist (post res))
  : prop
  = ST.tree_ens t sl0 res sl1_ST <==>
   (post_eq_src (post_src_of_shape t s res) sl0 sl1_ST /\
    tree_ens (repr_SF_of_ST t s sl0) res (sel_SF_of_ST post s.shp res sl1_ST))

let ens_equiv_rev #a #pre #post (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre) (res : a) (sl1_SF : post_v (post_SF_of_ST post s.shp) res)
  : Lemma (requires ens_equiv t s sl0 res (sel_ST_of_SF t s sl0 res sl1_SF))
          (ensures  ST.tree_ens t sl0 res (sel_ST_of_SF t s sl0 res sl1_SF) <==>
                    tree_ens (repr_SF_of_ST t s sl0) res sl1_SF)
  =
    let src = post_src_of_shape t s res in
    let bij = post_bij s.shp            in
    sell_ST_of_SF_eq_src src bij sl0 sl1_SF;
    sel_SF_ST_SF t s sl0 res sl1_SF


/// The soundness (and completeness) lemmas:

val repr_SF_of_ST_req
      (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
      (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre)
  : Lemma (req_equiv t s sl0)

val repr_SF_of_ST_ens
      (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
      (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre) (res : a) (sl1 : Fl.flist (post res))
  : Lemma (ens_equiv t s sl0 res sl1)

val repr_SF_of_ST_rall_equiv
      (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
      (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre)
  : Lemma ((ST.tree_req t sl0 <==> tree_req (repr_SF_of_ST_rall t s sl0)) /\
           (forall (x : a) (sl1 : Fl.flist (post x)) .
             ST.tree_ens t sl0 x sl1 <==> tree_ens (repr_SF_of_ST_rall t s sl0) x sl1))


val repr_SF_of_ST_shape
      (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
      (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre)
  : Lemma (prog_has_shape (repr_SF_of_ST t s sl0) (shape_SF_of_ST s.shp))

val repr_SF_of_ST_rall_shape
      (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
      (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre)
  : Lemma (prog_has_shape (repr_SF_of_ST_rall t s sl0) (shape_SF_of_ST_rall s.shp))


(*** Steel.Repr.SF --> Repr.Fun *)

(**) val __begin_repr_fun_of_steel : unit

module Fun = Experiment.Repr.Fun


(***** [sl_tys] *)

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

noeq
type sl_tys_r (ty : sl_tys_t u#a u#b) : Type u#(max a (b + 1)) = {
  vl : ty.val_t;
  sl : Dl.dlist (ty.sel_t vl)
}

/// By using [Fl.flist_of_d'] instead of [Fl.flist_of_d], we force the normalization of [x.sl], which improves
/// the normalization time of [elim_returns].
let sl_v_of_r (#ty : sl_tys_t u#a u#b) (x : sl_tys_r ty) : sl_tys_v ty = {
  val_v = x.vl;
  sel_v = Fl.flist_of_d' x.sl;
}

let sl_r_of_v (#ty : sl_tys_t u#a u#b) (x : sl_tys_v ty) : sl_tys_r ty = {
  vl = x.val_v;
  sl = Fl.dlist_of_f x.sel_v;
}

let sl_vrv (ty : sl_tys_t u#a u#b) (x : sl_tys_v ty)
  : Lemma (sl_v_of_r (sl_r_of_v x) == x) [SMTPat (sl_v_of_r (sl_r_of_v x))]
  = ()

let sl_rvr (ty : sl_tys_t u#a u#b) (x : sl_tys_r ty)
  : Lemma (sl_r_of_v (sl_v_of_r x) == x) [SMTPat (sl_r_of_v (sl_v_of_r x))]
  = ()


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
let sl_tys' : Fun.tys' u#(max a b + 1) u#(max a (b + 1)) u#(max a (b + 1)) = {
  t = sl_tys_t u#a u#b;
  v = sl_tys_v u#a u#b;
  r = sl_tys_r u#a u#b;
  v_of_r = sl_v_of_r;
  r_of_v = sl_r_of_v;
  unit = {val_t = U.unit'; sel_t = (fun _ -> [])};
  emp  = {val_v = U.Unit'; sel_v = Fl.nil};
  all  = sl_all;
  ex   = sl_ex;
}

val sl_tys_hyp : unit -> Lemma (Fun.tys_hyp (sl_tys' u#a u#b))

let sl_tys : Fun.tys u#(max a b + 1) u#(max a (b + 1)) u#(max a (b + 1)) =
  (**) sl_tys_hyp ();
  sl_tys'


let delayed_sl_uncurrify
      (#val_t : Type) (#sel_t : post_t val_t) (#dst : Type)
      (f : (v : val_t) -> (sls : Fl.flist (sel_t v)) -> dst)
      (x : sl_tys_v ({val_t; sel_t})) : dst
  = f x.val_v x.sel_v 

unfold
let sl_tys_lam' : Fun.tys_lam' sl_tys = {
  lam_prop = (fun #src f -> delayed_sl_uncurrify #src.val_t #src.sel_t (fun val_v sel_v -> f ({val_v; sel_v})));
  lam_tree = (fun #src f -> delayed_sl_uncurrify #src.val_t #src.sel_t (fun val_v sel_v -> f ({val_v; sel_v})));
}

val sl_tys_lam_id : unit -> Lemma (Fun.tys_lam_id sl_tys_lam')

let sl_tys_lam : Fun.tys_lam sl_tys =
  (**) sl_tys_lam_id ();
  sl_tys_lam'


(***** Translation of the representation *)

let rec repr_Fun_of_SF (#val_t : Type u#a) (#sel_t : post_t u#a u#b val_t) (t : prog_tree val_t sel_t)
  : Tot (Fun.prog_tree u#(max a b + 1) u#(max a (b + 1)) u#(max a (b + 1)) u#a
                       #(sl_tys u#a u#b) ({val_t; sel_t}))
        (decreases t)
  = match t with
  | Tspec a post req ens ->
          Fun.Tspec ({val_t = a; sel_t = post}) req (sl_uncurrify ens)
  | Tret a x post sl ->
          Fun.Tret #sl_tys ({val_t = a; sel_t = post}) ({vl = x; sl})
  | Tbind a b itm post f g ->
          Fun.Tbind _ _ (repr_Fun_of_SF f) (sl_uncurrify (fun x sls -> repr_Fun_of_SF (g x sls)))
  | TbindP a b post wp f g ->
          Fun.TbindP a ({val_t = b; sel_t = post}) wp f (fun (x : a) -> repr_Fun_of_SF (g x))

let rec shape_Fun_of_SF (#post_n : nat) (s : shape_tree post_n)
  : Tot (Fun.shape_tree) (decreases s)
  = match s with
  | Sspec _           -> Fun.Sspec
  | Sret  smp_ret _   -> Fun.Sret smp_ret
  | Sbind _ _ s_f s_g -> Fun.Sbind  (shape_Fun_of_SF s_f) (shape_Fun_of_SF s_g)
  | SbindP  _ s_g     -> Fun.SbindP (shape_Fun_of_SF s_g)

(***** soundness of SF --> Fun *)

val repr_Fun_of_SF_req (#val_t : Type) (#sel_t : post_t val_t) (t : prog_tree u#a u#b val_t sel_t)
  : Lemma (tree_req t <==> Fun.tree_req (repr_Fun_of_SF t))

val repr_Fun_of_SF_ens (#val_t : Type) (#sel_t : post_t val_t) (t : prog_tree u#a u#b val_t sel_t)
                       (val_v : val_t) (sel_v : Fl.flist (sel_t val_v))
  : Lemma (tree_ens t val_v sel_v <==> Fun.tree_ens (repr_Fun_of_SF t) ({val_v; sel_v}))

val repr_Fun_of_SF_shape
      (#val_t : Type) (#sel_t : post_t val_t) (t : prog_tree u#a u#b val_t sel_t)
      (s : prog_shape t)
  : Lemma (Fun.prog_has_shape (repr_Fun_of_SF t) (shape_Fun_of_SF s.shp))
