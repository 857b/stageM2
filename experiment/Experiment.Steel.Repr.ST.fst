module Experiment.Steel.Repr.ST

module U    = Learn.Util
module M    = Experiment.Steel.Repr.M
module L    = FStar.List.Pure
module Uv   = FStar.Universe
module Dl   = Learn.DList
module Lf   = Learn.ListFun
module Perm = Learn.Permutation

open Experiment.Steel.Repr.M
open Steel.Effect.Common


type pre_t = Dl.ty_list
type post_t (a : Type) = Lf.list_fun a Type
unfold
let  post_ts (#a : Type) (post : post_t a) : a -> Dl.ty_list = post.lf_list
unfold
let  post_t_of_ts (a : Type) : Dl.ty_list -> post_t a = Lf.const a
unfold
let  append_post_t (#a : Type) : post_t a -> post_t a -> post_t a = Lf.append #a #Type

type req_t (pre : pre_t) = Dl.dlist pre -> prop
type ens_t (pre : pre_t) (a : Type) (post : post_t a) = Dl.dlist pre -> (x : a) -> Dl.dlist (post_ts post x) -> prop


/// unit for an arbitrary universe
type unit' : Type u#a = | Unit' : unit'

noeq
type prog_tree : (a : Type u#a) -> (pre : pre_t u#b) -> (post : post_t u#a u#b a) -> Type u#(1 + max a b) =
  | Tequiv : (pre : Dl.ty_list) -> (post : Dl.ty_list) ->
             (p : Perm.pequiv pre post) ->
             prog_tree unit' pre (post_t_of_ts unit' post)
  | Tspec  : (a : Type u#a) -> (pre : pre_t) -> (post : post_t a) -> (frame : Dl.ty_list) ->
             (req : req_t pre) -> (ens : ens_t pre a post) ->
             prog_tree a L.(pre@frame) (append_post_t post (post_t_of_ts a frame))
  | Tret   : (a : Type u#a) -> (x : a) -> (post : post_t a) ->
             prog_tree a (post_ts post x) post
  | Tbind  : (a : Type u#a) -> (b : Type u#a) ->
             (pre : pre_t) -> (itm : post_t a) -> (post : post_t b) ->
             (f : prog_tree a pre itm) -> (g : ((x : a) -> prog_tree b (post_ts itm x) post)) ->
             prog_tree b pre post
  | TbindP : (a : Type u#a) -> (b : Type u#a) ->
             (pre : pre_t) -> (post : post_t b) ->
             (wp : pure_wp a) -> (x : unit -> PURE a wp) -> (g : a -> prog_tree b pre post) ->
             prog_tree b pre post

noeq
type shape_tree : (pre_n : nat) -> (post_n : nat) -> Type =
  | Sequiv : (n : nat) -> (p : Perm.perm_f n) ->
             shape_tree n n
  | Sspec  : (pre_n : nat) -> (post_n : nat) -> (frame_n : nat) ->
             shape_tree (pre_n + frame_n) (post_n + frame_n)
  | Sret   : (n : nat) ->
             shape_tree n n
  | Sbind  : (pre_n : nat) -> (itm_n : nat) -> (post_n : nat) ->
             (f : shape_tree pre_n itm_n) -> (g : shape_tree itm_n post_n) ->
             shape_tree pre_n post_n
  | SbindP : (pre_n : nat) -> (post_n : nat) ->
             (g : shape_tree pre_n post_n) ->
             shape_tree pre_n post_n

let rec prog_has_shape (#a : Type u#a) (#pre : pre_t u#b) (#post : post_t u#a u#b a)
                       (t : prog_tree a pre post) (s : shape_tree (L.length pre) (post.lf_len))
  : Tot prop (decreases t)
  = match t returns prop with
  | Tequiv pre post p           -> s == Sequiv _ p
  | Tspec  _ pre post frame _ _ -> s == Sspec  (L.length pre) (post.lf_len) (L.length frame)
  | Tret   _ _ post             -> s == Sret   _
  | Tbind  a _ pre itm post f g -> exists (s_f : shape_tree (L.length pre) itm.lf_len)
                                    (s_g : shape_tree itm.lf_len     post.lf_len) .
                                  s == Sbind _ _ _ s_f s_g /\
                                  prog_has_shape f s_f /\
                                  (forall (x : a) . prog_has_shape (g x) s_g)
  | TbindP a _ pre post _ _ g   -> exists (s_g : shape_tree (L.length pre) post.lf_len) .
                                  s == SbindP _ _ s_g /\
                                  (forall (x : a) . prog_has_shape (g x) s_g)

type prog_shape (#a : Type) (#pre : pre_t) (#post : post_t a) (t : prog_tree a pre post)
  = s : shape_tree (L.length pre) (post.lf_len) {prog_has_shape t s}

(* TODO ? r can requires t == t0*) 
unfold
let match_prog_tree
      (#a0 : Type u#a) (#pre0 : pre_t u#b) (#post0 : post_t u#a u#b a0)
      (t0 : prog_tree a0 pre0 post0)
      (r : (a : Type u#a) -> (pre : pre_t u#b) -> (post : post_t u#a u#b a) ->
           (t : prog_tree a pre post) -> Type u#c)
      (c_Tequiv : (pre : Dl.ty_list) -> (post : Dl.ty_list) ->
                  (p : Perm.pequiv pre post) ->
                  Pure (r _ _ _ (Tequiv pre post p))
                       (requires a0 == unit' /\ pre0 == pre /\ post0 == (post_t_of_ts unit' post) /\
                                 t0 == Tequiv pre post p)
                       (ensures fun _ -> True))
      (c_Tspec  : (a : Type) -> (pre : pre_t) -> (post : post_t a) -> (frame : Dl.ty_list) ->
                  (req : req_t pre) -> (ens : ens_t pre a post) ->
                  Pure (r _ _ _ (Tspec a pre post frame req ens))
                       (requires a0 == a /\ pre0 == L.(pre@frame) /\
                                 post0 == append_post_t post (post_t_of_ts a frame) /\
                                 t0 == Tspec a pre post frame req ens)
                       (ensures fun _ -> True))
      (c_Tret   : (a : Type) -> (x : a) -> (post : post_t a) ->
                  Pure (r _ _ _ (Tret a x post))
                       (requires a0 == a /\ pre0 == (post_ts post x) /\ post0 == post /\
                                 t0 == Tret a x post)
                       (ensures fun _ -> True))
      (c_Tbind  : (a : Type) -> (b : Type) ->
                  (pre : pre_t) -> (itm : post_t a) -> (post : post_t b) ->
                  (f : prog_tree a pre itm {f << t0}) ->
                  (g : ((x : a) -> prog_tree b (post_ts itm x) post) {forall (x : a) . {:pattern (g x)} g x << t0}) ->
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
    | Tequiv pre post p               -> c_Tequiv pre post p
    | Tspec  a pre post frame req ens -> c_Tspec  a pre post frame req ens
    | Tret   a x post                 -> c_Tret   a x post
    | Tbind  a b pre itm post f g     -> c_Tbind  a b pre itm post f g
    | TbindP a b pre post wp x g      -> c_TbindP a b pre post wp x g


let bind (#a : Type) (#b : Type) (#pre : pre_t) (#itm : post_t a) (#post : post_t b)
         (f : prog_tree a pre itm) (g : (x:a) -> prog_tree b (post_ts itm x) post)
  : prog_tree b pre post
  = Tbind a b pre itm post f g

(* TODO? generalize Experiment.Steel.Repr.M.bind_req... *)
let rec tree_req (#a : Type) (#pre : pre_t) (#post : post_t a) (t : prog_tree a pre post)
  : Tot (req_t pre) (decreases t)
  = match t with
  | Tequiv _ _ _ ->
             (fun sl0 -> True)
  | Tspec _  pre _ frame  req _ ->
             (fun sl0 -> req (Dl.splitAt_ty pre frame sl0)._1)
  | Tret _ _ _ ->
             (fun sl0 -> True)
  | Tbind a _  _ itm _  f g ->
             (fun sl0 -> tree_req f sl0 /\
               (forall (x : a) (sl1 : Dl.dlist (post_ts itm x)) . tree_ens f sl0 x sl1 ==> tree_req (g x) sl1))
  | TbindP a _  _ _  wp _ g ->
             (fun sl0 -> wp (fun (x : a) -> tree_req (g x) sl0) /\ True)

and tree_ens (#a : Type) (#pre : pre_t) (#post : post_t a) (t : prog_tree a pre post)
  : Tot (ens_t pre a post) (decreases t)
  = match t with
  | Tequiv _ post p ->
             (fun sl0 x sl1 ->
               sl1 == Dl.apply_pequiv p sl0)
  | Tspec a  pre post frame  req ens ->
             (fun sl0 x sl1 ->
               let sl0', frame0 = Dl.splitAt_ty pre              frame sl0 in
               let sl1', frame1 = Dl.splitAt_ty (post_ts post x) frame sl1 in
               frame1 == frame0 /\ ens sl0' x sl1')
  | Tret _ x post ->
             (fun sl0 x' sl1 -> x' == x /\ sl1 == sl0)
  | Tbind a _  _ itm _  f g ->
             (fun sl0 y sl2 -> tree_req f sl0 /\
               (exists (x : a) (sl1 : Dl.dlist (post_ts itm x)) . tree_ens f sl0 x sl1 /\ tree_ens (g x) sl1 y sl2))
  | TbindP a _  _ _  wp _ g ->
             (fun sl0 y sl1 -> as_requires wp /\ (exists (x : a) . as_ensures wp x /\ tree_ens (g x) sl0 y sl1))


(*** Repr.M --> Repr.ST *)

module T = FStar.Tactics
open FStar.Calc

unfold
let post_ST_of_M (#a : Type) (post : M.post_t a) : post_t a
  = Lf.map Mkvprop'?.t post

let rec repr_ST_of_M (#a : Type u#a) (t : M.prog_tree a)
                     (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
  : Tot (prog_tree a (vprop_list_sels_t pre) (post_ST_of_M post))
        (decreases t)
  = match c with
  | TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1 ->
             Tequiv (vprop_list_sels_t pre') (vprop_list_sels_t L.(pre@frame)) (vequiv_sl p0);;
             (**) L.map_append Mkvprop'?.t pre frame;
             x <-- Tspec a (vprop_list_sels_t pre) (post_ST_of_M post)
                          (vprop_list_sels_t frame) req ens;
             (**) L.map_append Mkvprop'?.t (post_vp post x) frame;
             Tequiv (vprop_list_sels_t L.(post_vp post x@frame))
                    (vprop_list_sels_t (post_vp post' x))
                    (vequiv_sl (p1 x));;
             Tret _ x (post_ST_of_M post')
  | TCret #a #x  pre post  p ->
             Tequiv (vprop_list_sels_t pre) (vprop_list_sels_t (post_vp post x)) (vequiv_sl p);;
             Tret _ x (post_ST_of_M post)
  | TCbind #a #b #f #g  pre itm post  cf cg ->
             x <-- repr_ST_of_M f cf;
             repr_ST_of_M (g x) (cg x)
  | TCbindP #a #b #wp #x #g  pre post  cg ->
             TbindP a b _ _ wp x (fun x -> repr_ST_of_M (g x) (cg x))


let norm_tree_spec () : T.Tac unit
  = T.norm [delta_only [`%repr_ST_of_M; `%bind; `%tree_req; `%tree_ens];
            delta_attr [`%Lf.__list_fun__; `%U.__util_func__];
            delta_qualifier ["unfold"];
            zeta; iota; simplify]

#push-options "--z3rlimit 15"
let repr_ST_of_M__TCspec_ens
      #a #pre #post (req : M.req_t pre) (ens : M.ens_t pre a post)
      (pre' : M.pre_t) (post' : M.post_t a) (frame : vprop_list)
      (p0 : vequiv pre' L.(pre @ frame)) (p1 : (x : a) -> vequiv (post_vp post x @ frame) (post_vp post' x))
      (sl0' : sl_t pre') (res : a) (sl1' : sl_t (post_vp post' res))

  : Lemma (
    (**) L.map_append Mkvprop'?.t pre frame;
    (**) L.map_append Mkvprop'?.t (post_vp post res) frame;

    (tree_ens (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1)) sl0' res sl1'
    <==> (let sl0, frame0 = Dl.splitAt_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                             (Dl.apply_pequiv (vequiv_sl p0) sl0') in
        let sl1, frame1 = Dl.splitAt_ty (vprop_list_sels_t (post_vp post res)) (vprop_list_sels_t frame)
                             (Dl.apply_pequiv (Perm.pequiv_sym (vequiv_sl (p1 res))) sl1') in
        req sl0 /\ frame1 == frame0 /\ ens sl0 res sl1)))
  =
    L.map_append Mkvprop'?.t pre frame;
    L.map_append Mkvprop'?.t (post_vp post res) frame;
    assert (
      tree_ens (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1)) sl0' res sl1'
    <==> (exists (sl1f : Dl.dlist L.(vprop_list_sels_t (post_vp post res) @ vprop_list_sels_t frame)) .
          let sl0, frame0 = Dl.splitAt_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                               (Dl.apply_pequiv (vequiv_sl p0) sl0') in
          let sl1, frame1 = Dl.splitAt_ty (vprop_list_sels_t (post_vp post res)) (vprop_list_sels_t frame) sl1f in
          sl1' == Dl.apply_pequiv (vequiv_sl (p1 res)) sl1f /\
          req sl0 /\ frame1 == frame0 /\ ens sl0 res sl1))
      by T.(norm_tree_spec (); smt ());
    introduce forall (sl1f : Dl.dlist L.(vprop_list_sels_t (post_vp post res) @ vprop_list_sels_t frame)) .
        sl1' == Dl.apply_pequiv (vequiv_sl (p1 res)) sl1f <==>
        sl1f == Dl.apply_pequiv (Perm.pequiv_sym (vequiv_sl (p1 res))) sl1'
      with Dl.apply_pequiv_sym_eq_iff (vequiv_sl (p1 res)) sl1f sl1';

    assert (tree_ens (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1)) sl0' res sl1'
    <==> (let sl0, frame0 = Dl.splitAt_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                             (Dl.apply_pequiv (vequiv_sl p0) sl0') in
        let sl1, frame1 = Dl.splitAt_ty (vprop_list_sels_t (post_vp post res)) (vprop_list_sels_t frame)
                             (Dl.apply_pequiv (Perm.pequiv_sym (vequiv_sl (p1 res))) sl1') in
        req sl0 /\ frame1 == frame0 /\ ens sl0 res sl1))
#pop-options


/// Remark: the equivalence of the ensures clauses holds only when the requires clause is satisfied

#push-options "--z3rlimit 30"
let rec repr_ST_of_M_req (#a : Type) (t : M.prog_tree a)
                         (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
                         (sl0 : sl_t pre)
  : Lemma (ensures M.tree_req t c sl0 <==> tree_req (repr_ST_of_M t c) sl0)
  = match c as c returns squash (M.tree_req t c sl0 <==> tree_req (repr_ST_of_M t c) sl0) with
  | TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1 ->
             L.map_append Mkvprop'?.t pre frame;

             calc (<==>) {
               M.tree_req _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1) sl0;
             <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ()) }
               req (extract_vars_f pre' pre frame p0 sl0)._1;
             <==> { assert_norm (extract_vars_f pre' pre frame p0 sl0
                    == Dl.splitAt_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                         (Dl.apply_pequiv (vequiv_sl p0) sl0)) }
               req (Dl.splitAt_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                              (Dl.apply_pequiv (vequiv_sl p0) sl0))._1;
             <==> { assert (tree_req (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1)) sl0
                     <==> req (Dl.splitAt_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                              (Dl.apply_pequiv (vequiv_sl p0) sl0))._1)
                 by T.(norm_tree_spec (); smt ()) }
               tree_req (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1)) sl0;
             <==> { U.f_equal tree_req (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1))
                                     (repr_ST_of_M _ c) }
               tree_req (repr_ST_of_M _ c) sl0;
             }

  | TCret #a #x  pre post  p ->
             U.f_equal tree_req (repr_ST_of_M _ (TCret #a #x pre post p))
                                (repr_ST_of_M _ c);
             assert (M.tree_req _ (TCret #a #x pre post p) sl0 == True) by T.(trefl ());
             assert (tree_req (repr_ST_of_M _ (TCret #a #x pre post p)) sl0 <==> True)
                    by T.(norm_tree_spec (); smt ())

  | TCbind #a #b #f #g  pre itm post  cf cg ->
             let r0 = repr_ST_of_M _ (TCbind #a #b #f #g  pre itm post  cf cg) in
             let r1 = repr_ST_of_M _ c in
             U.f_equal tree_req r0 r1;

             calc (<==>) {
               M.tree_req _ (TCbind #a #b #f #g  pre itm post  cf cg) sl0;
             <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
               bind_req (M.tree_req f cf) (M.tree_ens f cf) (fun x -> M.tree_req (g x) (cg x)) sl0;
             <==> {
               repr_ST_of_M_req f cf sl0;
               introduce forall (x : a) (sl1 : sl_t (post_vp itm x)) .
                 tree_req (repr_ST_of_M f cf) sl0 ==>
                 (M.tree_ens f cf sl0 x sl1 <==> tree_ens (repr_ST_of_M f cf) sl0 x sl1) /\
                 (M.tree_req (g x) (cg x) sl1 <==> tree_req (repr_ST_of_M (g x) (cg x)) sl1)
               with introduce _ ==> _
               with _ . (repr_ST_of_M_ens f cf sl0 x sl1; repr_ST_of_M_req (g x) (cg x) sl1)
             }
               tree_req (repr_ST_of_M f cf) sl0 /\
               (forall (x : a) (sl1 : Dl.dlist (vprop_list_sels_t (post_vp itm x))) .
                 tree_ens (repr_ST_of_M f cf) sl0 x sl1 ==> tree_req (repr_ST_of_M (g x) (cg x)) sl1);
             <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
               tree_req (repr_ST_of_M _ (TCbind #a #b #f #g  pre itm post  cf cg)) sl0;
             <==> {}
               tree_req r0 sl0;
             <==> { assert (r0 == r1) }
               tree_req r1 sl0;
             }

  | TCbindP #a #b #wp #x #g  pre post  cg ->
            calc (<==>) {
              M.tree_req _ c sl0;
            <==> {}
              M.tree_req _ (TCbindP #a #b #wp #x #g pre post cg) sl0;
            <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
              bind_pure_req wp (fun x -> M.tree_req (g x) (cg x)) sl0;
            <==> {
              FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
              introduce forall (x : a).
                 (M.tree_req (g x) (cg x) sl0 <==> tree_req (repr_ST_of_M (g x) (cg x)) sl0)
               with repr_ST_of_M_req (g x) (cg x) sl0
            }
              wp (fun x -> tree_req (repr_ST_of_M (g x) (cg x)) sl0) /\ True;
            <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
              tree_req (repr_ST_of_M _ (TCbindP #a #b #wp #x #g pre post cg)) sl0;
            <==> {U.f_equal tree_req (repr_ST_of_M _ (TCbindP #a #b #wp #x #g pre post cg)) (repr_ST_of_M _ c)}
              tree_req (repr_ST_of_M _ c) sl0;
            }

and repr_ST_of_M_ens (#a : Type) (t : M.prog_tree a)
                     (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
                     (sl0 : sl_t pre) (res : a) (sl1 : sl_t (post_vp post res))
  : Lemma (requires M.tree_req t c sl0)
          (ensures M.tree_ens t c sl0 res sl1 <==> tree_ens (repr_ST_of_M t c) sl0 res sl1)
  = match c as c returns squash (M.tree_ens t c sl0 res sl1 <==> tree_ens (repr_ST_of_M t c) sl0 res sl1) with
    | TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1 ->
             L.map_append Mkvprop'?.t pre frame;
             L.map_append Mkvprop'?.t (post_vp post res) frame;

             calc (<==>) {
               M.tree_ens _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1) sl0 res sl1;
             <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ()) }
              (let fsl0, frame0 = extract_vars_f pre' pre frame p0 sl0 in
               let fsl1, frame1 = extract_vars_f (post_vp post' res) (post_vp post res) frame
                                                 (Perm.pequiv_sym (p1 res)) sl1 in
                frame1 == frame0 /\ ens fsl0 res fsl1);
             <==> { (* since req holds *) }
              (let fsl0, frame0 = Dl.splitAt_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                                                  (Dl.apply_pequiv (vequiv_sl p0) sl0) in
               let fsl1, frame1 = Dl.splitAt_ty (vprop_list_sels_t (post_vp post res)) (vprop_list_sels_t frame)
                                                  (Dl.apply_pequiv (Perm.pequiv_sym (vequiv_sl (p1 res))) sl1) in
                req fsl0 /\ frame1 == frame0 /\ ens fsl0 res fsl1);
             <==> {repr_ST_of_M__TCspec_ens req ens pre' post' frame p0 p1 sl0 res sl1}
               tree_ens (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame p0 p1)) sl0 res sl1;
             <==> {U.f_equal tree_ens (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1))
                                    (repr_ST_of_M _ c)}
               tree_ens (repr_ST_of_M _ c) sl0 res sl1;
             }

  | TCret #a #x  pre post  p ->
             calc (<==>) {
               M.tree_ens _ (TCret #a #x pre post p) sl0 res sl1;
             <==> { assert (M.tree_ens _ (TCret #a #x pre post p) sl0 res sl1 <==>
                           (res == x /\ sl1 == extract_vars p sl0))
                      by T.(norm [delta_only [`%M.tree_ens]; zeta; iota]; smt ()) }
               res == x /\ sl1 == extract_vars p sl0;
             <==> {}
               res == x /\ sl1 == Dl.apply_pequiv (vequiv_sl p) sl0;
             <==> { assert (tree_ens (repr_ST_of_M _ (TCret #a #x pre post p)) sl0 res sl1 <==>
                           (res == x /\ sl1 == Dl.apply_pequiv (vequiv_sl p) sl0))
                      by T.(norm_tree_spec (); smt ()) }
               tree_ens (repr_ST_of_M _ (TCret #a #x pre post p)) sl0 res sl1;
             <==> { U.f_equal tree_ens (repr_ST_of_M _ (TCret #a #x pre post p))
                                    (repr_ST_of_M _ c) }
               tree_ens (repr_ST_of_M _ c) sl0 res sl1;
             }

  | TCbind #a #b #f #g  pre itm post  cf cg ->
             calc (<==>) {
               M.tree_ens _ (TCbind #a #b #f #g  pre itm post  cf cg) sl0 res sl1;
             <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
               bind_ens (M.tree_req f cf) (M.tree_ens f cf) (fun x -> M.tree_ens (g x) (cg x)) sl0 res sl1;
             <==> {
               repr_ST_of_M_req f cf sl0;
               introduce forall (x : a) (sl1' : sl_t (post_vp itm x)) .
                 tree_req (repr_ST_of_M f cf) sl0 ==>
                 (M.tree_ens f cf sl0 x sl1' <==> tree_ens (repr_ST_of_M f cf) sl0 x sl1') /\
                 (M.tree_ens f cf sl0 x sl1' ==> (
                 (M.tree_ens (g x) (cg x) sl1' res sl1 <==> tree_ens (repr_ST_of_M (g x) (cg x)) sl1' res sl1)))
               with introduce _ ==> _ with _ . introduce _ /\ _
               with repr_ST_of_M_ens f cf sl0 x sl1'
                and introduce _ ==> _
                with _ . repr_ST_of_M_ens (g x) (cg x) sl1' res sl1
             }
               tree_req (repr_ST_of_M f cf) sl0 /\
               (exists (x : a) (sl1' : Dl.dlist (vprop_list_sels_t (post_vp itm x))) .
                 tree_ens (repr_ST_of_M f cf) sl0 x sl1' /\
                 tree_ens (repr_ST_of_M (g x) (cg x)) sl1' res sl1);
             <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
               tree_ens (repr_ST_of_M _ (TCbind #a #b #f #g  pre itm post  cf cg)) sl0 res sl1;
             <==> {U.f_equal tree_ens (repr_ST_of_M _ (TCbind #a #b #f #g pre itm post cf cg))
                                    (repr_ST_of_M _ c)}
               tree_ens (repr_ST_of_M _ c) sl0 res sl1;
             }

  | TCbindP #a #b #wp #x #g  pre post  cg ->
            calc (<==>) {
              M.tree_ens _ c sl0 res sl1;
            <==> {}
              M.tree_ens _ (TCbindP #a #b #wp #x #g pre post cg) sl0 res sl1;
            <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
              bind_pure_ens wp (fun x -> M.tree_ens (g x) (cg x)) sl0 res sl1;
            <==> {
              assert (M.tree_req _ (TCbindP #a #b #wp #x #g pre post cg) sl0
                   == (wp (fun x -> M.tree_req (g x) (cg x) sl0) /\ True))
                 by T.(trefl ());
              U.prop_equal (fun p -> p) (M.tree_req _ (TCbindP #a #b #wp #x #g pre post cg) sl0)
                                     (wp (fun x -> M.tree_req (g x) (cg x) sl0) /\ True);
              FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
              introduce forall (x : a).
                 as_ensures wp x ==>
                 (M.tree_ens (g x) (cg x) sl0 res sl1 <==> tree_ens (repr_ST_of_M (g x) (cg x)) sl0 res sl1)
               with introduce _ ==> _
               with _ . repr_ST_of_M_ens (g x) (cg x) sl0 res sl1
            }
              as_requires wp /\ (exists (x : a) . as_ensures wp x /\ tree_ens (repr_ST_of_M (g x) (cg x)) sl0 res sl1);
            <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
              tree_ens (repr_ST_of_M _ (TCbindP #a #b #wp #x #g pre post cg)) sl0 res sl1;
            <==> {U.f_equal tree_ens (repr_ST_of_M _ (TCbindP #a #b #wp #x #g pre post cg))
                                   (repr_ST_of_M _ c)}
              tree_ens (repr_ST_of_M _ c) sl0 res sl1;
            }
#pop-options



(* --------------------------- *)

open Steel.Reference

let test_ST (r : ref nat) = repr_ST_of_M (test_M r).repr_tree (test_cond r)

//let _ = fun r ->
// assert (print_util (test_ST r))
//    by T.(norm normal_spec_steps; qed ())

let test_ST_shape =
  Sbind 1 1 1 (Sbind 1 1 1 (Sequiv 1 (Perm.id_n 1))
              (Sbind 1 1 1 (Sspec  1 1 0)
              (Sbind 1 1 1 (Sequiv 1 (Perm.id_n 1))
                           (Sret   1))))
              (Sbind 1 1 1 (Sequiv 1 (Perm.id_n 1))
                           (Sret   1))

let rec prog_has_shape' (#a : Type u#a) (#pre : pre_t u#b) (#post : post_t u#a u#b a)
                        (t : prog_tree a pre post) (s : shape_tree (L.length pre) (post.lf_len))
  : Pure prop (requires True) (ensures fun p -> p <==> prog_has_shape t s) (decreases t)
  = match t returns prop with
  | Tequiv pre post p           -> (match s with
                                  | Sequiv _ p' -> p' == p
                                  | _ -> False)
  | Tspec  _ pre post frame _ _ -> (match s with
                                  | Sspec  pre_n post_n frame_n ->
                                      pre_n == L.length pre /\ post_n == post.lf_len /\ frame_n == L.length frame
                                  | _ -> False)
  | Tret   _ _ post             -> (match s with
                                  | Sret   _ -> True
                                  | _ -> False)
  | Tbind  a _ pre itm post f g -> (match s with
                                  | Sbind _ itm_n _ s_f s_g ->
                                      itm_n == itm.lf_len /\
                                      prog_has_shape' f s_f /\
                                      (forall (x : a) . prog_has_shape' (g x) s_g)
                                  | _ -> False)
  | TbindP a _ pre post _ _ g   -> (match s with
                                  | SbindP _ _ s_g -> (forall (x : a) . prog_has_shape' (g x) s_g)
                                  | _ -> False)


let test_ST_has_shape (r : ref nat)
  : squash (prog_has_shape' (test_ST r) test_ST_shape)
  = _ by T.(norm normal_spec_steps; norm [simplify]; smt ())
