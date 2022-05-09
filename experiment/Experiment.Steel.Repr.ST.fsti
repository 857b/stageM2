module Experiment.Steel.Repr.ST

module U    = Learn.Util
module M    = Experiment.Steel.Repr.M
module L    = FStar.List.Pure
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


(***** Shape *)

noeq
type shape_tree : (pre_n : nat) -> (post_n : nat) -> Type =
  | Sequiv : (n : nat) -> (p : Perm.perm_f n) ->
             shape_tree n n
  | Sframe : (pre_n : nat) -> (post_n : nat) -> (frame_n : nat) ->
             (f : shape_tree pre_n post_n) ->
             shape_tree (pre_n + frame_n) (post_n + frame_n)
  | Sspec  : (pre_n : nat) -> (post_n : nat) ->
             shape_tree pre_n post_n
  | Sret   : (n : nat) ->
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
    | Tspec  _ pre post _ _       -> s == Sspec  (L.length pre) post_n /\
                                    (forall (x : a) . L.length (post x) == post_n)
    | Tret   _ _ post             -> post_n = L.length pre /\
                                    s == Sret   _
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
                                  | Sret   _ -> (forall (x : a) . post_n = L.length (post x))
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
  | TCret #a #x  pre post  p ->
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
        Sbind _ _ _ (Sequiv (pre_n  + frame_n) p0) (
        Sbind _ _ _ (Sframe pre_n post_n frame_n (Sspec  pre_n post_n)) (
        Sbind _ _ _ (Sequiv (post_n + frame_n) p1)
                    (Sret   (post_n + frame_n))))
  | M.Sret n p ->
        Sbind _ _ _ (Sequiv n p) (Sret n)
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
