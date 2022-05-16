module Experiment.Steel.Repr.ST

module U    = Learn.Util
module M    = Experiment.Steel.Repr.M
module L    = FStar.List.Pure
module T    = FStar.Tactics
module Fl   = Learn.FList
module Perm = Learn.Permutation

open Experiment.Steel.Repr.M
open Steel.Effect.Common


type pre_t = Fl.ty_list
type post_t (a : Type) = a -> Fl.ty_list

type req_t (pre : pre_t) = Fl.flist pre -> prop
type ens_t (pre : pre_t) (a : Type) (post : post_t a) = Fl.flist pre -> (x : a) -> Fl.flist (post x) -> prop

let const_post (#a : Type) (ts : Fl.ty_list) : post_t a = fun _ -> ts
let frame_post (#a : Type) (pt : post_t a) (fr : Fl.ty_list) : post_t a = fun (x : a) -> L.(pt x @ fr)

noeq
type prog_tree : (a : Type u#a) -> (pre : pre_t u#b) -> (post : post_t u#a u#b a) -> Type u#(1 + max a b) =
  | Tequiv : (pre : Fl.ty_list) -> (post : Fl.ty_list) ->
             (p : Perm.pequiv pre post) ->
             prog_tree U.unit' pre (const_post post)
  | Tframe : (a : Type u#a) -> (pre : Fl.ty_list) -> (post : post_t a) -> (frame : Fl.ty_list) ->
             (f : prog_tree a pre post) ->
             prog_tree a L.(pre @ frame) (frame_post post frame)
  | Tspec  : (a : Type u#a) -> (pre : pre_t) -> (post : post_t a) ->
             (req : req_t pre) -> (ens : ens_t pre a post) ->
             prog_tree a pre post
  | Tret   : (a : Type u#a) -> (x : a) -> (post : post_t a) ->
             prog_tree a (post x) post
  | Tbind  : (a : Type u#a) -> (b : Type u#a) ->
             (pre : pre_t) -> (itm : post_t a) -> (post : post_t b) ->
             (f : prog_tree a pre itm) -> (g : ((x : a) -> prog_tree b (itm x) post)) ->
             prog_tree b pre post
  | TbindP : (a : Type u#a) -> (b : Type u#a) ->
             (pre : pre_t) -> (post : post_t b) ->
             (wp : pure_wp a) -> (x : unit -> PURE a wp) -> (g : a -> prog_tree b pre post) ->
             prog_tree b pre post


(* TODO ? r can requires t == t0*) 
unfold
let match_prog_tree
      (#a0 : Type u#a) (#pre0 : pre_t u#b) (#post0 : post_t u#a u#b a0)
      (t0 : prog_tree a0 pre0 post0)
      (r : (a : Type u#a) -> (pre : pre_t u#b) -> (post : post_t u#a u#b a) ->
           (t : prog_tree a pre post) -> Type u#c)
      (c_Tequiv : (pre : Fl.ty_list) -> (post : Fl.ty_list) ->
                  (p : Perm.pequiv pre post) ->
                  Pure (r _ _ _ (Tequiv pre post p))
                       (requires a0 == U.unit' /\ pre0 == pre /\ post0 == const_post post /\
                                 t0 == Tequiv pre post p)
                       (ensures fun _ -> True))
      (c_Tframe : (a : Type) -> (pre : pre_t) -> (post : post_t a) -> (frame : Fl.ty_list) ->
                  (f : prog_tree a pre post {f << t0}) ->
                  Pure (r _ _ _ (Tframe a pre post frame f))
                       (requires a0 == a /\ pre0 == L.(pre @ frame) /\
                                 post0 == frame_post post frame /\
                                 t0 == Tframe a pre post frame f)
                       (ensures fun _ -> True))
      (c_Tspec  : (a : Type) -> (pre : pre_t) -> (post : post_t a) ->
                  (req : req_t pre) -> (ens : ens_t pre a post) ->
                  Pure (r _ _ _ (Tspec a pre post req ens))
                       (requires a0 == a /\ pre0 == pre /\
                                 post0 == post /\
                                 t0 == Tspec a pre post req ens)
                       (ensures fun _ -> True))
      (c_Tret   : (a : Type) -> (x : a) -> (post : post_t a) ->
                  Pure (r _ _ _ (Tret a x post))
                       (requires a0 == a /\ pre0 == post x /\ post0 == post /\
                                 t0 == Tret a x post)
                       (ensures fun _ -> True))
      (c_Tbind  : (a : Type) -> (b : Type) ->
                  (pre : pre_t) -> (itm : post_t a) -> (post : post_t b) ->
                  (f : prog_tree a pre itm {f << t0}) ->
                  (g : ((x : a) -> prog_tree b (itm x) post) {forall (x : a) . {:pattern (g x)} g x << t0}) ->
                  Pure (r _ _ _ (Tbind a b pre itm post f g))
                       (requires a0 == b /\ pre0 == pre /\ post0 == post /\
                                 t0 == Tbind a b pre itm post f g)
                       (ensures fun _ -> True))
      (c_TbindP : (a : Type) -> (b : Type) ->
                  (pre : pre_t) -> (post : post_t b) ->
                  (wp : pure_wp a) -> (x : (unit -> PURE a wp)) ->
                  (g : (a -> prog_tree b pre post) {forall (x : a) . {:pattern (g x)} g x << t0}) ->
                  Pure (r _ _ _ (TbindP a b pre post wp x g))
                       (requires a0 == b /\ pre0 == pre /\ post0 == post /\
                                 t0 == TbindP a b pre post wp x g)
                       (ensures fun _ -> True))
  : r _ _ _ t0
  = match t0 as t returns r _ _ _ t with
    | Tequiv pre post p           -> c_Tequiv pre post p
    | Tframe a pre post frame f   -> c_Tframe a pre post frame f
    | Tspec  a pre post req ens   -> c_Tspec  a pre post req ens
    | Tret   a x post             -> c_Tret   a x post
    | Tbind  a b pre itm post f g -> c_Tbind  a b pre itm post f g
    | TbindP a b pre post wp x g  -> c_TbindP a b pre post wp x g

unfold
let bind (#a : Type) (#b : Type) (#pre : pre_t) (#itm : post_t a) (#post : post_t b)
         (f : prog_tree a pre itm) (g : (x:a) -> prog_tree b (itm x) post)
  : prog_tree b pre post
  = Tbind a b pre itm post f g

(* TODO? generalize Experiment.Steel.Repr.M.bind_req... *)
let rec tree_req (#a : Type) (#pre : pre_t) (#post : post_t a) (t : prog_tree a pre post)
  : Tot (req_t pre) (decreases t)
  = match t with
  | Tequiv _ _ _ ->
             (fun sl0 -> True)
  | Tframe _ pre _ frame f ->
             (fun sl0 -> tree_req f (Fl.splitAt_ty pre frame sl0)._1)
  | Tspec _  _ _  req _ ->
             req
  | Tret _ _ _ ->
             (fun sl0 -> True)
  | Tbind a _  _ itm _  f g ->
             (fun sl0 -> tree_req f sl0 /\
               (forall (x : a) (sl1 : Fl.flist (itm x)) . tree_ens f sl0 x sl1 ==> tree_req (g x) sl1))
  | TbindP a _  _ _  wp _ g ->
             (fun sl0 -> wp (fun (x : a) -> tree_req (g x) sl0) /\ True)

and tree_ens (#a : Type) (#pre : pre_t) (#post : post_t a) (t : prog_tree a pre post)
  : Tot (ens_t pre a post) (decreases t)
  = match t with
  | Tequiv _ post p ->
             (fun sl0 _ sl1 ->
               sl1 == Fl.apply_pequiv p sl0)
  | Tframe a  pre post frame f ->
             (fun sl0 x sl1 ->
               let sl0', frame0 = Fl.splitAt_ty pre      frame sl0 in
               let sl1', frame1 = Fl.splitAt_ty (post x) frame sl1 in
               frame1 == frame0 /\ tree_ens f sl0' x sl1')
  | Tspec _  _ _  _ ens ->
             ens
  | Tret _ x post ->
             (fun sl0 x' sl1 -> x' == x /\ sl1 == sl0)
  | Tbind a _  _ itm _  f g ->
             (fun sl0 y sl2 ->
               (exists (x : a) (sl1 : Fl.flist (itm x)) . tree_ens f sl0 x sl1 /\ tree_ens (g x) sl1 y sl2))
  | TbindP a _  _ _  wp _ g ->
             (fun sl0 y sl1 -> (exists (x : a) . as_ensures wp x /\ tree_ens (g x) sl0 y sl1))

(***** [equiv] *)

let equiv (#a : Type) (#pre : pre_t) (#post : post_t a) (f g : prog_tree a pre post) : prop =
  (forall (sl0 : Fl.flist pre) . tree_req f sl0 <==> tree_req g sl0) /\
  (forall (sl0 : Fl.flist pre) . tree_req f sl0 ==>
    (forall (res : a) (sl1 : Fl.flist (post res)) .
      tree_ens f sl0 res sl1 <==> tree_ens g sl0 res sl1))


val equiv_Tframe
      (#a : Type) (#pre : pre_t) (#post : post_t a) (frame : Fl.ty_list)
      (f f' : prog_tree a pre post) (eq_f : squash (equiv f f'))
  : squash (equiv (Tframe a pre post frame f) (Tframe a pre post frame f'))

val equiv_Tbind
      (#a #b : Type) (#pre : pre_t) (#itm : post_t a) (#post : post_t b)
      (f f' : prog_tree a pre itm) (g g' : (x : a) -> prog_tree b (itm x) post)
      (eq_f : squash (equiv f f')) (eq_g : (x : a) -> squash (equiv (g x) (g' x)))
  : squash (equiv (Tbind a b pre itm post f g) (Tbind a b pre itm post f' g'))

val equiv_TbindP
      (#a #b : Type) (#pre : pre_t) (#post : post_t b) (wp : pure_wp a)
      (f : unit -> PURE a wp) (g g' : (x : a) -> prog_tree b pre post)
      (eq_g : (x : a) -> squash (equiv (g x) (g' x)))
  : squash (equiv (TbindP a b pre post wp f g) (TbindP a b pre post wp f g'))

val equiv_Tbind_assoc_Tbind
      (#a #b #c : Type) (#pre : pre_t) (#itm0 : post_t a) (#itm1 : post_t b) (#post : post_t c)
      (f : prog_tree a pre itm0)
      (g : (x : a) -> prog_tree b (itm0 x) itm1)
      (h : (y : b) -> prog_tree c (itm1 y) post)
  : squash (equiv (bind (bind f g) h) (bind f (fun x -> bind (g x) h)))

(* NOTE: the following:

   val equiv_TbindP_assoc_Tbind (#a #b #c : Type) (#pre : pre_t) (#itm : post_t a) (#post : post_t b)
      (wp : pure_wp a) (f : unit -> PURE a wp)
      (g : (x : a) -> prog_tree b pre itm)
      (h : (y : b) -> prog_tree c (itm y) post)
   : squash (equiv (bind (TbindP _ _ _ _ wp f g) h) (TbindP _ _ _ _ wp f (fun x -> bind (g x) h)))

   seems false because the reverse direction of:
     wp pt <==> (as_requires wp /\ (forall (x : a) . as_ensures wp x ==> pt x))
   does not hold with our assumptions an wp.
*)

(***** Shape *)

(**) val __begin_shape : unit

noeq
type shape_tree : (pre_n : nat) -> (post_n : nat) -> Type =
  | Sequiv : (n : nat) -> (p : Perm.perm_f n) ->
             shape_tree n n
  | Sframe : (pre_n : nat) -> (post_n : nat) -> (frame_n : nat) ->
             (f : shape_tree pre_n post_n) ->
             shape_tree (pre_n + frame_n) (post_n + frame_n)
  | Sspec  : (pre_n : nat) -> (post_n : nat) ->
             shape_tree pre_n post_n
  | Sret   : (smp_ret : bool) -> (n : nat) ->
             shape_tree n n
  | Sbind  : (pre_n : nat) -> (itm_n : nat) -> (post_n : nat) ->
             (f : shape_tree pre_n itm_n) -> (g : shape_tree itm_n post_n) ->
             shape_tree pre_n post_n
  | SbindP : (pre_n : nat) -> (post_n : nat) ->
             (g : shape_tree pre_n post_n) ->
             shape_tree pre_n post_n

let post_has_len (#a : Type) (post : post_t a) (len : nat) : prop = forall (x : a) . L.length (post x) = len

let rec prog_has_shape (#a : Type u#a) (#pre : pre_t u#b) (#post : post_t u#a u#b a)
                       (t : prog_tree a pre post)
                       (#post_n : nat) (s : shape_tree (L.length pre) post_n)
  : Pure prop (requires True)
              (ensures fun p -> p ==> post_has_len post post_n)
              (decreases t)
  =
    post_has_len post post_n /\
    (match t returns prop with
    | Tequiv pre post p           -> post_n = L.length pre /\ s == Sequiv _ p
    | Tframe _ pre post frame f   -> exists (post'_n : nat)
                                      (s_f : shape_tree (L.length pre) post'_n) .
                                    post_n = post'_n + L.length frame /\
                                    s == Sframe (L.length pre) post'_n (L.length frame) s_f /\
                                    prog_has_shape f s_f
    | Tspec  _ pre post _ _       -> s == Sspec  (L.length pre) post_n
    | Tret   _ _ post             -> exists (smp_ret : bool) .
                                    post_n = L.length pre /\
                                    s == Sret   smp_ret _
    | Tbind  a b pre itm post f g -> exists (itm_n : nat)
                                      (s_f : shape_tree (L.length pre) itm_n)
                                      (s_g : shape_tree itm_n          post_n) .
                                    s == Sbind _ _ _ s_f s_g /\
                                    prog_has_shape f s_f /\
                                    (forall (x : a) . prog_has_shape (g x) s_g)
    | TbindP a _ pre post _ _ g   -> exists (s_g : shape_tree (L.length pre) post_n) .
                                    s == SbindP _ _ s_g /\
                                   (forall (x : a) . prog_has_shape (g x) s_g)
    )

let rec prog_has_shape' (#a : Type u#a) (#pre : pre_t u#b) (#post : post_t u#a u#b a)
                        (t : prog_tree a pre post)
                        (#post_n : nat) (s : shape_tree (L.length pre) post_n)
  : Pure prop (requires True) (ensures fun p -> p <==> prog_has_shape t s) (decreases t)
  = match t returns prop with
  | Tequiv pre post p           -> (match s with
                                  | Sequiv _ p' -> p' == p
                                  | _ -> False)
  | Tframe _ pre post frame f   -> (match s with
                                  | Sframe pre_n post_n frame_n s_f ->
                                      pre_n   = L.length pre /\
                                      frame_n = L.length frame /\
                                      prog_has_shape' f s_f
                                  | _ -> False)
  | Tspec  _ pre post  _ _      -> (match s with
                                  | Sspec  pre_n post_n ->
                                     (forall (x : a) . post_n = L.length (post x))
                                  | _ -> False)
  | Tret   _ _ post             -> (match s with
                                  | Sret   _ _ -> (forall (x : a) . post_n = L.length (post x))
                                  | _ -> False)
  | Tbind  a b pre itm post f g -> (match s with
                                  | Sbind _ itm_n _ s_f s_g ->
                                      prog_has_shape' f s_f /\
                                      (forall (x : a) . prog_has_shape' (g x) s_g) /\
                                      (forall (y : b) . post_n = L.length (post y))
                                  | _ -> False)
  | TbindP a b pre post _ _ g   -> (match s with
                                  | SbindP _ _ s_g ->
                                      (forall (x : a) . prog_has_shape' (g x) s_g) /\
                                      (forall (y : b) . post_n = L.length (post y))
                                  | _ -> False)


noeq
type prog_shape (#a : Type) (#pre : pre_t) (#post : post_t a) (t : prog_tree a pre post) = {
  post_len : (l : nat {post_has_len post l});
  shp      : (s : shape_tree (L.length pre) post_len {prog_has_shape t s});
}

unfold
let mk_prog_shape (#a : Type) (#pre : pre_t) (#post : post_t a) (t : prog_tree a pre post)
                  (#post_len : nat) (shp : shape_tree (L.length pre) post_len {prog_has_shape t shp})
  : prog_shape t =
  { post_len; shp}


(*** Repr.M --> Repr.ST *)

let post_ST_of_M (#a : Type) (post : M.post_t a) : post_t a
  = fun (x : a) -> vprop_list_sels_t (post x)

let rec repr_ST_of_M (#a : Type) (t : M.prog_tree u#a a)
                     (#pre0 : M.pre_t) (#post0 : M.post_t a) (c : M.tree_cond t pre0 post0)
  : Tot (prog_tree a (vprop_list_sels_t pre0) (post_ST_of_M post0))
        (decreases t)
  = match c with
  | TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1 ->
             Tequiv (vprop_list_sels_t pre') (vprop_list_sels_t L.(pre@frame)) (vequiv_sl p0);;
             (**) L.map_append Mkvprop'?.t pre frame;
             x <-- Tframe a (vprop_list_sels_t pre) (post_ST_of_M post) (vprop_list_sels_t frame)
                 (Tspec a (vprop_list_sels_t pre) (post_ST_of_M post) req ens);
             (**) L.map_append Mkvprop'?.t (post x) frame;
             Tequiv (vprop_list_sels_t L.(post x @ frame))
                    (vprop_list_sels_t (post' x))
                    (vequiv_sl (p1 x));;
             Tret _ x (post_ST_of_M post')
  | TCret #a #x #_  pre post  p ->
             Tequiv (vprop_list_sels_t pre) (vprop_list_sels_t (post x)) (vequiv_sl p);;
             Tret _ x (post_ST_of_M post)
  | TCbind #a #b #f #g  pre itm post  cf cg ->
             x <-- repr_ST_of_M f cf;
             repr_ST_of_M (g x) (cg x)
  | TCbindP #a #b #wp #x #g  pre post  cg ->
             TbindP a b _ _ wp x (fun x -> repr_ST_of_M (g x) (cg x))


let rec shape_ST_of_M (#pre_n : nat) (#post_n : nat) (s : M.shape_tree pre_n post_n)
  : Tot (shape_tree pre_n post_n) (decreases s)
  = match s with
  | M.Sspec pre_n post_n frame_n p0 p1 ->
        Sbind _ _ _ (Sequiv (pre_n  + frame_n) (Perm.perm_f_of_list p0)) (
        Sbind _ _ _ (Sframe pre_n post_n frame_n (Sspec  pre_n post_n)) (
        Sbind _ _ _ (Sequiv (post_n + frame_n) (Perm.perm_f_of_list p1))
                    (Sret   true (post_n + frame_n))))
  | M.Sret n p ->
        Sbind _ _ _ (Sequiv n (Perm.perm_f_of_list p)) (Sret false n)
  | M.Sbind _ _ _ f g -> Sbind  _ _ _ (shape_ST_of_M f) (shape_ST_of_M g)
  | M.SbindP _ _ g    -> SbindP _ _ (shape_ST_of_M g)
                    


(**** soundness of M --> ST *)

val repr_ST_of_M_req (#a : Type) (t : M.prog_tree u#a a)
                     (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
                     (sl0 : sl_t pre)
  : Lemma (M.tree_req t c sl0 <==> tree_req (repr_ST_of_M t c) sl0)

val repr_ST_of_M_ens (#a : Type) (t : M.prog_tree u#a a)
                     (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
                     (sl0 : sl_t pre) (res : a) (sl1 : sl_t (post res))
  : Lemma (M.tree_ens t c sl0 res sl1 <==> tree_ens (repr_ST_of_M t c) sl0 res sl1)


val repr_ST_of_M_shape
      (#a : Type) (t : M.prog_tree u#a a)
      (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
      (#post_n : nat) (s : M.shape_tree (L.length pre) post_n)
   : Lemma (requires M.tree_cond_has_shape c s)
           (ensures  prog_has_shape (repr_ST_of_M t c) (shape_ST_of_M s))


(*** Binders flattening *)

// TODO? simplify using something similar to [Repr.Fun.elim_returns]

let flatten_prog_k_id #a #post #pre' (t' : prog_tree a pre' post) : prog_tree a pre' post
  = t'

let rec flatten_prog
      #a #pre #post (t : prog_tree a pre post)
  : Tot (prog_tree a pre post) (decreases %[t; 1])
  = flatten_prog_aux t flatten_prog_k_id

and flatten_prog_aux
      #a  #pre #post (t : prog_tree a pre post)
      #a1 #post1 (k : ((#pre' : pre_t) -> (t' : prog_tree a pre' post) -> prog_tree a1 pre' post1))
  : Tot (prog_tree a1 pre post1) (decreases %[t; 0])
  = match t with
  | Tequiv _ _ _ | Tspec _ _ _ _ _ | Tret _ _ _ -> k t
  | Tframe a pre post frame f ->
             k (Tframe a pre post frame (flatten_prog f))
  | Tbind  a b pre itm post f g ->
             flatten_prog_aux f (fun #pre' f' ->
               Tbind a a1 pre' itm post1 f' (fun (x : a) ->
                 flatten_prog_aux (g x) k))
  | TbindP a b pre post wp f g ->
             // we do not flatten the TbindP since we would need [equiv_Tbind_assoc_Tbind]
             k (TbindP a b pre post wp f (fun (x : a) ->
               flatten_prog (g x)))


let flatten_shape_k_id #post_n #pre'_n (t' : shape_tree pre'_n post_n) : shape_tree pre'_n post_n
  = t'

let rec flatten_shape
      #pre_n #post_n (t : shape_tree pre_n post_n)
  : Tot (shape_tree pre_n post_n) (decreases %[t; 1])
  = flatten_shape_aux t flatten_shape_k_id

and flatten_shape_aux
      #pre_n #post_n (t : shape_tree pre_n post_n)
      #post1_n (k : ((#pre'_n : nat) -> (t' : shape_tree pre'_n post_n) -> shape_tree pre'_n post1_n))
  : Tot (shape_tree pre_n post1_n) (decreases %[t; 0])
  = match t with
  | Sequiv _ _ | Sspec _ _ | Sret _ _ -> k t
  | Sframe _ _ frame_n f ->
             k (Sframe _ _ frame_n (flatten_shape f))
  | Sbind  pre_n itm_n post_n f g ->
             flatten_shape_aux f (fun #pre'_n f' ->
               Sbind pre'_n itm_n post1_n f' (flatten_shape_aux g k))
  | SbindP _ _ g ->
             k (SbindP _ _ (flatten_shape g))



val flatten_equiv
      (#a : Type) (#pre : pre_t) (#post : post_t a) (t : prog_tree u#a u#b a pre post)
  : Lemma (equiv (flatten_prog t) t)

val flatten_equiv_aux
      (#a : Type) (#pre : pre_t) (#post : post_t a) (t : prog_tree u#a u#b a pre post)
      (#a1 : Type) (#post1 : post_t a1)
      (k : ((#pre' : pre_t) -> (t' : prog_tree a pre' post) -> prog_tree a1 pre' post1))
      (k_equiv : (pre' : pre_t) -> (t'0 : prog_tree a pre' post) -> (t'1 : prog_tree a pre' post) ->
                     Lemma (requires equiv t'0 t'1) (ensures equiv (k t'0) (k t'1)))
      (k_bind  : ((a0 : Type u#a) -> (pre' : pre_t) -> (itm : post_t a0) ->
                      (f : prog_tree a0 pre' itm) -> (g : ((x : a0) -> (prog_tree a (itm x) post))) ->
                     Lemma (equiv (k (Tbind a0 a pre' itm post f g))
                                  (Tbind a0 a1 pre' itm post1 f (fun x -> k (g x))))))
  : Lemma (equiv (flatten_prog_aux t k) (k t))

val flatten_prog_shape
      (#a : Type) (#pre : pre_t) (#post : post_t a) (t : prog_tree u#a u#b a pre post)
      (#post_n : nat) (s : shape_tree (L.length pre) post_n)
   : Lemma (requires prog_has_shape t s)
           (ensures  prog_has_shape (flatten_prog t) (flatten_shape s))

val flatten_prog_shape_aux
      (#a : Type) (#pre : pre_t) (#post : post_t a) (t : prog_tree u#a u#b a pre post)
      (#post_n : nat) (s : shape_tree (L.length pre) post_n)
      (#a1 : Type) (#post1 : post_t a1)
      (k_t : ((#pre' : pre_t) -> (t' : prog_tree a pre' post) -> prog_tree u#a u#b a1 pre' post1))
      (post1_n : nat {post_has_len post1 post1_n})
      (k_s : ((#pre'_n : nat) -> (s' : shape_tree pre'_n post_n) -> shape_tree pre'_n post1_n))
      (k_hyp : (pre' : pre_t) -> (t' : prog_tree a pre' post) -> (s' : shape_tree (L.length pre') post_n) ->
                   Lemma (requires prog_has_shape t' s') (ensures prog_has_shape (k_t t') (k_s s')))
   : Lemma (requires prog_has_shape t s)
           (ensures  prog_has_shape (flatten_prog_aux t k_t) (flatten_shape_aux s k_s))
