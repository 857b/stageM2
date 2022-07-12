module Experiment.Steel.Repr.SF

module Fl  = Learn.FList
module Dl  = Learn.DList
module ST  = Experiment.Steel.Repr.ST
module Fin = FStar.Fin


type post_t (a : Type) = a -> Fl.ty_list
type post_v (#a : Type) (post : post_t a) (x : a) = Fl.flist (post x)
type req_t = Type0
type ens_t (a : Type) (post : post_t a) = (x : a) -> post_v post x -> Type0

// TODO? Twp with a WP on the returned values and selectors
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
             (wp : pure_wp a) -> (g : a -> prog_tree b post) ->
             prog_tree b post
  | Tif    : (a : Type u#a) -> (guard : bool) ->
             (post : post_t a) ->
             (thn : prog_tree a post) -> (els : prog_tree a post) ->
             prog_tree a post

[@@ strict_on_arguments [2]] (* strict on t *)
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
  | TbindP a _  _  wp g ->
             wp (fun (x : a) -> tree_req (g x))
  | Tif a guard _ thn els ->
             tree_req (if guard then thn else els)

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
  | TbindP a _  post0  wp g ->
             (fun y (sl1 : post_v post y) ->
               (exists (x : a) . as_ensures wp x /\ tree_ens (g x) y sl1))
  | Tif a guard _ thn els ->
             tree_ens (if guard then thn else els)


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
  | Sif    : (post_n : nat) ->
             (thn : shape_tree post_n) -> (els : shape_tree post_n) ->
             shape_tree post_n

[@@ strict_on_arguments [2]] (* strict on t *)
let rec prog_has_shape (#a : Type u#a) (#post : post_t u#a u#b a)
                       (t : prog_tree a post)
                       (#post_n : nat) (s : shape_tree post_n)
  : Pure prop (requires True)
              (ensures fun p -> p ==> ST.post_has_len post post_n)
              (decreases t)
  =
    ST.post_has_len post post_n /\
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
    | TbindP a _ post _ g     -> exists (s_g : shape_tree post_n) .
                                s == SbindP _ s_g /\
                               (forall (x : a) . prog_has_shape (g x) s_g)
    | Tif a gd post thn els   -> exists (s_thn : shape_tree post_n)
                                  (s_els : shape_tree post_n) .
                                s == Sif _ s_thn s_els /\
                                prog_has_shape thn s_thn /\
                                prog_has_shape els s_els
    )

noeq
type prog_shape (#a : Type) (#post : post_t a) (t : prog_tree a post) = {
  post_len : (l : nat {ST.post_has_len post l});
  shp      : (s : shape_tree post_len {prog_has_shape t s});
}

unfold
let mk_prog_shape (#a : Type) (#post : post_t a) (t : prog_tree a post)
                  (#post_len : nat) (shp : shape_tree post_len {prog_has_shape t shp})
  : prog_shape t =
  { post_len; shp}


