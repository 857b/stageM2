module Experiment.Steel.Repr.ST

module U    = Learn.Util
module M    = Experiment.Steel.Repr.M
module L    = FStar.List.Pure
module Uv   = FStar.Universe
module Perm = Learn.Permutation

open Experiment.Steel.Repr.M
open Steel.Effect.Common


(* TODO? define vequiv for [list a] *)
let vequiv (ts0 ts1 : ty_list) = f : Perm.perm_f (L.length ts0) {ts1 == Perm.apply_perm_r f ts0}

unfold
let apply_vequiv (#ts0 #ts1 : ty_list) (f : vequiv ts0 ts1) (xs : var_list ts0) : var_list ts1
  = var_apply_perm_r f xs

unfold
let var_split_at_ty (ts0 ts1 : ty_list) (xs : var_list L.(ts0@ts1))
  : var_list ts0 & var_list ts1
  = L.lemma_append_splitAt ts0 ts1;
    var_splitAt (L.length ts0) xs


type pre_t = ty_list
type post_t (a : Type) = a -> ty_list
type req_t (pre : pre_t) = var_list pre -> prop
type ens_t (pre : pre_t) (a : Type) (post : post_t a) = var_list pre -> (x : a) -> var_list (post x) -> prop


type unit' : Type u#a = | Unit' : unit'

noeq
type prog_tree : (a : Type u#a) -> (pre : pre_t u#b) -> (post : post_t u#a u#b a) -> Type u#(1 + max a b) =
  | Tequiv : (pre : ty_list) -> (post : ty_list) ->
             (p : vequiv pre post) ->
             prog_tree unit' pre (fun _ -> post)
  | Tspec  : (a : Type u#a) -> (pre : pre_t) -> (post : post_t a) -> (frame : ty_list) ->
             (req : req_t pre) -> (ens : ens_t pre a post) ->
             prog_tree a L.(pre@frame) (fun (x : a) -> L.(post x @ frame))
  | Tret   : (a : Type u#a) -> (x : a) -> (post : post_t a) ->
             prog_tree a (post x) post
  | Tbind  : (a : Type u#a) -> (b : Type u#a) ->
             (pre : pre_t) -> (itm : (a -> ty_list)) -> (post : post_t b) ->
             (f : prog_tree a pre itm) -> (g : ((x : a) -> prog_tree b (itm x) post)) ->
             prog_tree b pre post
  | TbindP : (a : Type u#a) -> (b : Type u#a) ->
             (pre : pre_t) -> (post : post_t b) ->
             (wp : pure_wp a) -> (x : unit -> PURE a wp) -> (g : a -> prog_tree b pre post) ->
             prog_tree b pre post

let bind (#a : Type) (#b : Type) (#pre : pre_t) (#itm : a -> ty_list) (#post : post_t b)
         (f : prog_tree a pre itm) (g : (x:a) -> prog_tree b (itm x) post)
  : prog_tree b pre post
  = Tbind a b pre itm post f g

(* TODO? generalize Experiment.Steel.Repr.M.bind_req... *)
let rec tree_req (#a : Type) (#pre : pre_t) (#post : post_t a) (t : prog_tree a pre post)
  : Tot (req_t pre) (decreases t)
  = match t with
  | Tequiv _ _ _ ->
             (fun sl0 -> True)
  | Tspec _  pre _ frame  req _ ->
             (fun sl0 -> req (var_split_at_ty pre frame sl0)._1)
  | Tret _ _ _ ->
             (fun sl0 -> True)
  | Tbind a _  _ itm _  f g ->
             (fun sl0 -> tree_req f sl0 /\
               (forall (x : a) (sl1 : var_list (itm x)) . tree_ens f sl0 x sl1 ==> tree_req (g x) sl1))
  | TbindP a _  _ _  wp _ g ->
             (fun sl0 -> wp (fun (x : a) -> tree_req (g x) sl0) /\ True)

and tree_ens (#a : Type) (#pre : pre_t) (#post : post_t a) (t : prog_tree a pre post)
  : Tot (ens_t pre a post) (decreases t)
  = match t with
  | Tequiv _ _ p ->
             (fun sl0 _ sl1 -> sl1 == apply_vequiv p sl0)
  | Tspec _  pre post frame  req ens ->
             (fun sl0 x sl1 ->
               let sl0', frame0 = var_split_at_ty pre      frame sl0 in
               let sl1', frame1 = var_split_at_ty (post x) frame sl1 in
               frame1 == frame0 /\ ens sl0' x sl1')
  | Tret _ x post ->
             (fun sl0 x' sl1 -> x' == x /\ sl1 == sl0)
  | Tbind a _  _ itm _  f g ->
             (fun sl0 y sl2 -> tree_req f sl0 /\
               (exists (x : a) (sl1 : var_list (itm x)) . tree_ens f sl0 x sl1 /\ tree_ens (g x) sl1 y sl2))
  | TbindP a _  _ _  wp _ g ->
             (fun sl0 y sl1 -> as_requires wp /\ (exists (x : a) . as_ensures wp x /\ tree_ens (g x) sl0 y sl1))


(*** Repr.M --> Repr.ST *)

module T = FStar.Tactics
open FStar.Calc

unfold
let vequiv_of_M (#src #dst : vprop_list) (p : M.vequiv src dst)
  : Pure (vequiv (vprop_list_sels_t src) (vprop_list_sels_t dst))
         (requires True) (ensures fun p' ->
           U.cast #(Perm.perm_f (L.length (vprop_list_sels_t src))) (Perm.perm_f (L.length src)) p' == p)
  = Perm.map_apply_r p Mkvprop'?.t src;
    U.cast #(Perm.perm_f (L.length src)) (Perm.perm_f (L.length (vprop_list_sels_t src))) p

let rec repr_ST_of_M (#a : Type u#a) (t : M.prog_tree a)
                     (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
  : Tot (prog_tree a (vprop_list_sels_t pre) (fun (x : a) -> vprop_list_sels_t (post x)))
        (decreases t)
  = match c with
  | TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1 ->
             Tequiv (vprop_list_sels_t pre') (vprop_list_sels_t L.(pre@frame)) (vequiv_of_M p0);;
             (**) L.map_append Mkvprop'?.t pre frame;
             x <-- Tspec a (vprop_list_sels_t pre) (fun (x : a) -> vprop_list_sels_t (post x))
                          (vprop_list_sels_t frame) req ens;
             (**) L.map_append Mkvprop'?.t (post x) frame;
             Tequiv (vprop_list_sels_t L.(post x@frame)) (vprop_list_sels_t (post' x)) (vequiv_of_M (p1 x));;
             Tret _ x (fun x -> vprop_list_sels_t (post' x))
  | TCret #a #x  pre post  p ->
             Tequiv (vprop_list_sels_t pre) (vprop_list_sels_t (post x)) (vequiv_of_M p);;
             Tret _ x (fun x -> vprop_list_sels_t (post x))
  | TCbind #a #b #f #g  pre itm post  cf cg ->
             x <-- repr_ST_of_M f cf;
             repr_ST_of_M (g x) (cg x)
  | TCbindP #a #b #wp #x #g  pre post  cg ->
             TbindP a b _ _ wp x (fun x -> repr_ST_of_M (g x) (cg x))


let norm_tree_spec () : T.Tac unit
  = T.norm [delta_only [`%repr_ST_of_M; `%bind; `%tree_req; `%tree_ens];
            zeta; iota; simplify]

unfold
let vequiv_sym (#ts0 #ts1 : ty_list) (f : vequiv ts0 ts1) : vequiv ts1 ts0
  = 
    Perm.(calc (==) {
      apply_perm_r (inv_f f) ts1;
    == {}
      apply_perm_r (inv_f f) (apply_perm_r f ts0);
    == {apply_r_comp (inv_f f) f ts0}
      ts0;
    });
    U.cast #(Perm.perm_f (L.length ts0)) (Perm.perm_f (L.length ts1)) (Perm.inv_f f)

let vequiv_ts_eq (#ts0 #ts1 : ty_list) (f : vequiv ts0 ts1)
  : Lemma (ts1 == Perm.apply_perm_r f ts0)
  = ()

let apply_vequiv_sym_l (#ts0 #ts1 : ty_list) (f : vequiv ts0 ts1) (xs : var_list ts0)
  : Lemma (apply_vequiv (vequiv_sym f) (apply_vequiv f xs) == xs)
  =
    var_apply_r_comp (Perm.inv_f f) f xs

let apply_vequiv_sym_r (#ts0 #ts1 : ty_list) (f : vequiv ts0 ts1) (xs : var_list ts1)
  : Lemma (apply_vequiv f (apply_vequiv (vequiv_sym f) xs) == xs)
  =
    vequiv_ts_eq (vequiv_sym f);
    var_apply_r_comp f (Perm.inv_f f) xs


let apply_vequiv_sym_eq_iff (#ts0 #ts1 : ty_list) (f : vequiv ts0 ts1) (xs : var_list ts0) (ys : var_list ts1)
  : Lemma (xs == apply_vequiv (vequiv_sym f) ys <==> ys == apply_vequiv f xs)
  =
    apply_vequiv_sym_l f xs;
    apply_vequiv_sym_r f ys

#push-options "--z3rlimit 15"
let repr_ST_of_M__TCspec_ens
      #a #pre #post (req : M.req_t pre) (ens : M.ens_t pre a post)
      (pre' : M.pre_t) (post' : M.post_t a) (frame : vprop_list)
      (p0 : M.vequiv pre' L.(pre @ frame)) (p1 : (x : a) -> M.vequiv (post x @ frame) (post' x))
      (sl0' : sl_t pre') (res : a) (sl1' : sl_t (post' res))

  : Lemma (
    (**) L.map_append Mkvprop'?.t pre frame;
    (**) L.map_append Mkvprop'?.t (post res) frame;

    (tree_ens (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1)) sl0' res sl1'
    <==> (let sl0, frame0 = var_split_at_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                             (apply_vequiv (vequiv_of_M p0) sl0') in
        let sl1, frame1 = var_split_at_ty (vprop_list_sels_t (post res)) (vprop_list_sels_t frame)
                             (apply_vequiv (vequiv_sym (vequiv_of_M (p1 res))) sl1') in
        req sl0 /\ frame1 == frame0 /\ ens sl0 res sl1)))
  =
    L.map_append Mkvprop'?.t pre frame;
    L.map_append Mkvprop'?.t (post res) frame;
    assert (
      tree_ens (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1)) sl0' res sl1'
    <==> (exists (sl1f : var_list L.(vprop_list_sels_t (post res) @ vprop_list_sels_t frame)) .
          let sl0, frame0 = var_split_at_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                               (apply_vequiv (vequiv_of_M p0) sl0') in
          let sl1, frame1 = var_split_at_ty (vprop_list_sels_t (post res)) (vprop_list_sels_t frame) sl1f in
          sl1' == apply_vequiv (vequiv_of_M (p1 res)) sl1f /\
          req sl0 /\ frame1 == frame0 /\ ens sl0 res sl1))
      by T.(norm_tree_spec (); smt ());
    
    introduce forall (sl1f : var_list L.(vprop_list_sels_t (post res) @ vprop_list_sels_t frame)) .
        sl1' == apply_vequiv (vequiv_of_M (p1 res)) sl1f <==>
        sl1f == apply_vequiv (vequiv_sym (vequiv_of_M (p1 res))) sl1'
      with apply_vequiv_sym_eq_iff (vequiv_of_M (p1 res)) sl1f sl1';

    assert (tree_ens (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1)) sl0' res sl1'
    <==> (let sl0, frame0 = var_split_at_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                             (apply_vequiv (vequiv_of_M p0) sl0') in
        let sl1, frame1 = var_split_at_ty (vprop_list_sels_t (post res)) (vprop_list_sels_t frame)
                             (apply_vequiv (vequiv_sym (vequiv_of_M (p1 res))) sl1') in
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
                    == var_split_at_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                         (apply_vequiv (vequiv_of_M p0) sl0)) }
               req (var_split_at_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                              (apply_vequiv (vequiv_of_M p0) sl0))._1;
             <==> { assert (tree_req (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1)) sl0
                     <==> req (var_split_at_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                              (apply_vequiv (vequiv_of_M p0) sl0))._1)
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
               introduce forall (x : a) (sl1 : sl_t (itm x)) .
                 tree_req (repr_ST_of_M f cf) sl0 ==>
                 (M.tree_ens f cf sl0 x sl1 <==> tree_ens (repr_ST_of_M f cf) sl0 x sl1) /\
                 (M.tree_req (g x) (cg x) sl1 <==> tree_req (repr_ST_of_M (g x) (cg x)) sl1)
               with introduce _ ==> _
               with _ . (repr_ST_of_M_ens f cf sl0 x sl1; repr_ST_of_M_req (g x) (cg x) sl1)
             }
               tree_req (repr_ST_of_M f cf) sl0 /\
               (forall (x : a) (sl1 : var_list (vprop_list_sels_t (itm x))) .
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
                     (sl0 : sl_t pre) (res : a) (sl1 : sl_t (post res))
  : Lemma (requires M.tree_req t c sl0)
          (ensures M.tree_ens t c sl0 res sl1 <==> tree_ens (repr_ST_of_M t c) sl0 res sl1)
  = match c as c returns squash (M.tree_ens t c sl0 res sl1 <==> tree_ens (repr_ST_of_M t c) sl0 res sl1) with
    | TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1 ->
             L.map_append Mkvprop'?.t pre frame;
             L.map_append Mkvprop'?.t (post res) frame;

             calc (<==>) {
               M.tree_ens _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1) sl0 res sl1;
             <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ()) }
              (let fsl0, frame0 = extract_vars_f pre' pre frame p0 sl0 in
               let fsl1, frame1 = extract_vars_f (post' res) (post res) frame (M.vequiv_sym (p1 res)) sl1 in
                frame1 == frame0 /\ ens fsl0 res fsl1);
             <==> { (* since req holds *) }
              (let fsl0, frame0 = var_split_at_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                                                  (apply_vequiv (vequiv_of_M p0) sl0) in
               let fsl1, frame1 = var_split_at_ty (vprop_list_sels_t (post res)) (vprop_list_sels_t frame)
                                                  (apply_vequiv (vequiv_sym (vequiv_of_M (p1 res))) sl1) in
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
               res == x /\ sl1 == apply_vequiv (vequiv_of_M p) sl0;
             <==> { assert (tree_ens (repr_ST_of_M _ (TCret #a #x pre post p)) sl0 res sl1 <==>
                           (res == x /\ sl1 == apply_vequiv (vequiv_of_M p) sl0))
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
               introduce forall (x : a) (sl1' : sl_t (itm x)) .
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
               (exists (x : a) (sl1' : var_list (vprop_list_sels_t (itm x))) .
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

let test_ST (r : ref nat) = repr_ST_of_M (test r).repr_tree (test_cond r)

//let _ = fun r ->
//  assert (print_util (test_ST r))
//    by T.(norm normal_spec_steps; qed ())
