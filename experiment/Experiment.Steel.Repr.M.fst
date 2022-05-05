module Experiment.Steel.Repr.M

module T    = FStar.Tactics
module U    = Learn.Util
module L    = FStar.List.Pure
module Uv   = FStar.Universe
module Dl   = Learn.DList
module Ll   = Learn.List
module Lf   = Learn.ListFun
module Mem  = Steel.Memory
module Perm = Learn.Permutation
module FExt = FStar.FunctionalExtensionality

open FStar.Calc
open FStar.Classical.Sugar

open Steel.Effect
open Steel.Effect.Atomic

#set-options "--ide_id_info_off"

irreducible let __tree_reduce__ : unit = ()


(** [vprop_list] *)

type vprop_list = list vprop'

let rec vprop_of_list (vpl : vprop_list) : vprop =
  match vpl with
  | [] -> emp
  | v :: vs -> VStar (VUnit v) (vprop_of_list vs)

let rec vprop_of_list_can_be_split (vs : vprop_list) (i : nat {i < L.length vs})
  : Lemma (ensures can_be_split (vprop_of_list vs) (VUnit (L.index vs i)))
  = let v :: vs = vs in
    if i = 0
    then can_be_split_star_l (VUnit v) (vprop_of_list vs)
    else begin
      can_be_split_star_r (VUnit v) (vprop_of_list vs);
      vprop_of_list_can_be_split vs (i-1);
      can_be_split_trans (VUnit v `star` vprop_of_list vs) (vprop_of_list vs) (VUnit (L.index vs (i-1)))
    end

let rec flatten_vprop_aux (vp : vprop) (acc : vprop_list) : GTot vprop_list =
  match vp with
  | VUnit vp' -> vp' :: acc
  | VStar vp0 vp1 -> flatten_vprop_aux vp0 (flatten_vprop_aux vp1 acc)

let flatten_vprop (vp : vprop) : GTot vprop_list = flatten_vprop_aux vp []

let rec flatten_vprop_aux_eq (vp : vprop) (acc : vprop_list)
  : Lemma (flatten_vprop_aux vp acc == L.(flatten_vprop vp @ acc))
  = match vp with
  | VUnit _ -> ()
  | VStar vp0 vp1 ->
          calc (==) {
            flatten_vprop_aux (VStar vp0 vp1) acc;
          == {}
            flatten_vprop_aux vp0 (flatten_vprop_aux vp1 acc);
          == {flatten_vprop_aux_eq vp0 (flatten_vprop_aux vp1 acc);
              flatten_vprop_aux_eq vp1 acc}
            L.(flatten_vprop vp0 @ (flatten_vprop vp1 @ acc));
          == {L.append_assoc (flatten_vprop vp0) (flatten_vprop vp1) acc}
            L.((flatten_vprop vp0 @ (flatten_vprop vp1 @ [])) @ acc);
          == {flatten_vprop_aux_eq vp1 [];
              flatten_vprop_aux_eq vp0 (flatten_vprop_aux vp1 [])}
            L.(flatten_vprop_aux (VStar vp0 vp1) [] @ acc);
          }

let flatten_vprop_VStar (vp0 vp1 : vprop)
  : Lemma (flatten_vprop (VStar vp0 vp1) == L.(flatten_vprop vp0 @ flatten_vprop vp1))
  =
    flatten_vprop_aux_eq vp0 (flatten_vprop_aux vp1 []);
    flatten_vprop_aux_eq vp1 []

let rec vprop_of_list_append (vs0 vs1 : vprop_list)
  : Lemma (ensures equiv (vprop_of_list L.(vs0@vs1)) (vprop_of_list vs0 `star` vprop_of_list vs1))
          (decreases vs0)
  = match vs0 with
  | []     -> assert (equiv (vprop_of_list vs1) (emp `star` vprop_of_list vs1))
                by (init_resolve_tac ())
  | v :: vs -> let v0 = VUnit v in
             let vl0 = vprop_of_list vs in
             let vl1 = vprop_of_list vs1 in
             let vl2 = vprop_of_list L.(vs @ vs1) in
             assert_norm (vprop_of_list L.((v :: vs) @ vs1) == v0 `star` vl2);
             equiv_refl v0;
             vprop_of_list_append vs vs1;
             star_congruence v0       vl2
                             v0 (vl0 `star` vl1);
             star_associative v0 vl0 vl1;
             equiv_sym ((v0 `star` vl0) `star` vl1) (v0 `star` (vl0 `star` vl1));
             
             equiv_trans (v0 `star` vl2)
                         (v0 `star` (vl0 `star` vl1))
                         ((v0 `star` vl0) `star` vl1);
             assert_norm (vprop_of_list (v :: vs) `star` vprop_of_list vs1
                      == (v0 `star` vl0) `star` vl1)

let rec vprop_equiv_flat (vp : vprop)
  : Lemma (equiv (vprop_of_list (flatten_vprop vp)) vp)
  = match vp with
  | VUnit v     -> assert (equiv (VUnit v `star` emp) (VUnit v))
                      by (init_resolve_tac ())
  | VStar v0 v1 -> flatten_vprop_VStar v0 v1;
                  vprop_of_list_append (flatten_vprop v0) (flatten_vprop v1);
                  vprop_equiv_flat v0;
                  vprop_equiv_flat v1;
                  star_congruence (vprop_of_list (flatten_vprop v0)) (vprop_of_list (flatten_vprop v1)) v0 v1;
                  equiv_trans (vprop_of_list L.(flatten_vprop v0 @ flatten_vprop v1))
                              (vprop_of_list (flatten_vprop v0) `star` vprop_of_list (flatten_vprop v1))
                              (v0 `star` v1)


(* ALT? dependent arrrow Fin.fin n -> _ *)

[@@ __tree_reduce__]
let vprop_list_sels_t : vprop_list -> Dl.ty_list =
  L.map Mkvprop'?.t

unfold
let sl_t (vs : vprop_list) : Type = Dl.dlist (vprop_list_sels_t vs)

let vprop_list_sels_t_eq (vs : vprop_list) (i : nat {i < L.length vs})
  : Lemma (ensures L.index (vprop_list_sels_t vs) i == (L.index vs i).t)
          [SMTPat (L.index (vprop_list_sels_t vs) i)]
  = Ll.map_index Mkvprop'?.t vs i

let rec vpl_sels (vs : vprop_list) (sl : t_of (vprop_of_list vs))
  : Tot (sl_t vs) (decreases vs)
  = match (|vs, sl|) <: (vs : vprop_list & t_of (vprop_of_list vs))  with
  | (|[], _|) -> Dl.DNil
  | (|v0 :: vs, (x0, xs)|) -> Dl.DCons v0.t x0 _ (vpl_sels vs xs)

unfold
let rmem_sels (#p:vprop) (vs : vprop_list)
    (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (vprop_of_list vs) /\ True)})
  : GTot (sl_t vs)
  = vpl_sels vs (h (vprop_of_list vs))

unfold
let split_vars (vs0 vs1 : vprop_list) (xs : sl_t (vs0@vs1))
  : sl_t vs0 & sl_t vs1
  =
    Ll.map_append Mkvprop'?.t vs0 vs1;
    Dl.splitAt_ty (vprop_list_sels_t vs0) (vprop_list_sels_t vs1) xs

let split_vars__cons (v0 : vprop') (vs0 vs1 : vprop_list) (x0 : v0.t) (xs : sl_t L.(vs0@vs1))
  : Lemma (ensures split_vars (v0 :: vs0) vs1 (Dl.DCons v0.t x0 (vprop_list_sels_t L.(vs0@vs1)) xs)
               == (let xs0, xs1 = split_vars vs0 vs1 xs in
                   Dl.DCons v0.t x0 (vprop_list_sels_t vs0) xs0, xs1))
  = Ll.map_append Mkvprop'?.t vs0 vs1

let rec steel_elim_vprop_of_list_append #opened (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list L.(vs0@vs1)) (fun () -> vprop_of_list vs0 `star` vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> split_vars vs0 vs1 (rmem_sels (vs0@vs1) h0) == (rmem_sels vs0 h1, rmem_sels vs1 h1))
      (decreases %[vs0; 0])
  =
    match vs0 with
    | [] -> change_equal_slprop (vprop_of_list L.(vs0@vs1)) (vprop_of_list vs1);
           change_equal_slprop emp (vprop_of_list vs0)
    | v0 :: vs0' -> steel_elim_vprop_of_list_append__cons vs0 vs1 v0 vs0'

and steel_elim_vprop_of_list_append__cons #opened (vs0 vs1 : vprop_list) v0 (vs0' : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list L.(vs0@vs1)) (fun () -> vprop_of_list vs0 `star` vprop_of_list vs1)
      (requires fun _ -> vs0 == v0 :: vs0')
      (ensures fun h0 () h1 -> split_vars vs0 vs1 (rmem_sels (vs0@vs1) h0) == (rmem_sels vs0 h1, rmem_sels vs1 h1))
      (decreases %[vs0'; 1])
  =
    change_equal_slprop (vprop_of_list L.(vs0@vs1)) (VUnit v0 `star` vprop_of_list L.(vs0'@vs1));
    (**) let sl_v0 : Ghost.erased (t_of (VUnit v0)) = gget (VUnit v0) in
    (**) let sl_vs01 : Ghost.erased (t_of (vprop_of_list L.(vs0'@vs1))) = gget (vprop_of_list L.(vs0'@vs1)) in
    steel_elim_vprop_of_list_append vs0' vs1;
    (**) let sl_vs0  = gget (vprop_of_list vs0') in
    (**) let sl_vs1  = gget (vprop_of_list vs1) in
    change_equal_slprop (VUnit v0 `star` vprop_of_list vs0') (vprop_of_list (vs0));
    calc (==) {
      split_vars (v0 :: vs0') vs1 (vpl_sels L.(v0 :: vs0' @ vs1) (Ghost.reveal sl_v0, Ghost.reveal sl_vs01));
    == {split_vars__cons v0 vs0' vs1 sl_v0 (vpl_sels L.(vs0' @ vs1) sl_vs01)}
      (let xs0, xs1 = split_vars vs0' vs1 (vpl_sels L.(vs0' @ vs1) sl_vs01) in
       Dl.DCons v0.t sl_v0 _ xs0, xs1);
    == {}
      Dl.DCons v0.t sl_v0 _ (vpl_sels vs0' sl_vs0), vpl_sels vs1 sl_vs1;
    }


let rec steel_intro_vprop_of_list_append #opened (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list vs0 `star` vprop_of_list vs1) (fun () -> vprop_of_list L.(vs0@vs1))
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> split_vars vs0 vs1 (rmem_sels (vs0@vs1) h1) == (rmem_sels vs0 h0, rmem_sels vs1 h0))
      (decreases vs0)
  = match vs0 with
    | [] -> change_equal_slprop (vprop_of_list vs0) emp;
           change_equal_slprop (vprop_of_list vs1) (vprop_of_list L.(vs0@vs1))
    | v0 :: vs0' ->
           change_equal_slprop (vprop_of_list (vs0)) (VUnit v0 `star` vprop_of_list vs0');
           (**) let sl_v0   = gget (VUnit v0) in
           steel_intro_vprop_of_list_append vs0' vs1;
           (**) let sl_vs01 = gget (vprop_of_list L.(vs0'@vs1)) in
           (**) split_vars__cons v0 vs0' vs1 sl_v0 (vpl_sels L.(vs0' @ vs1) sl_vs01);
           change_equal_slprop (VUnit v0 `star` vprop_of_list L.(vs0'@vs1)) (vprop_of_list L.(vs0@vs1))
           

(** [vequiv] *)

let vequiv : vprop_list -> vprop_list -> Type = Perm.pequiv #vprop'

unfold
let vequiv_sl (#vs0 #vs1 : vprop_list) (f : vequiv vs0 vs1)
  : Perm.pequiv (vprop_list_sels_t vs0) (vprop_list_sels_t vs1)
  = Perm.map_apply_r f Mkvprop'?.t vs0;
    U.cast #(Perm.perm_f (L.length vs0)) (Perm.perm_f (L.length (vprop_list_sels_t vs0))) f    

unfold
let extract_vars (#src #dst : vprop_list)
                 (p : vequiv src dst)
                 (xs : sl_t src)
  : sl_t dst
  =
    Dl.apply_pequiv (vequiv_sl p) xs

unfold
let extract_vars_f (src dst frame : vprop_list)
                   (p : vequiv src L.(dst@frame))
                   (xs : sl_t src)
  : sl_t dst & sl_t frame
  =
    split_vars dst frame (extract_vars p xs)

let extract_vars_sym_l (#vs0 #vs1 : vprop_list) (f : vequiv vs0 vs1) (xs : sl_t vs0)
  : Lemma (extract_vars (Perm.pequiv_sym f) (extract_vars f xs) == xs)
  =
    Dl.apply_pequiv_sym_l (vequiv_sl f) xs

/// applying a permutation on the context's vprop

let rec steel_change_swap (#opened:Mem.inames)
          (vs0 : vprop_list) (i : nat {i <= L.length vs0 - 2})
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list (Perm.list_swap i vs0))
      (requires fun _ -> True) (ensures fun h0 () h1 ->
        rmem_sels (Perm.list_swap i vs0) h1 === Dl.dlist_swap i (rmem_sels vs0 h0))
      (decreases i)
  = if i = 0
    then begin
      let v0 :: v1 :: vs = vs0 in
      change_equal_slprop (vprop_of_list vs0)
                          (VUnit v0 `star` (VUnit v1 `star` vprop_of_list vs));
      change_equal_slprop (VUnit v1 `star` (VUnit v0 `star` vprop_of_list vs))
                          (vprop_of_list (Perm.list_swap i vs0))
    end else begin
      let v0 :: vs = vs0 in
      change_equal_slprop (vprop_of_list vs0)
                          (VUnit v0 `star` vprop_of_list vs);
      steel_change_swap vs (i-1);
      change_equal_slprop (VUnit v0 `star` vprop_of_list (Perm.list_swap (i-1) vs))
                          (vprop_of_list (Perm.list_swap i vs0))
    end

let rec steel_change_vequiv_aux (#opened:Mem.inames)
          (n : nat) (vs0 vs1 : (l:vprop_list{L.length l == n}))
          (fs : list (i:nat{i <= n-2}))
          (eqv : squash (vs1 == Perm.apply_perm_r (Perm.comp_list (L.map (Perm.perm_f_swap #n) fs)) vs0))
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list vs1)
      (requires fun _ -> True) (ensures fun h0 () h1 ->
        rmem_sels vs1 h1 == extract_vars (Perm.comp_list (L.map Perm.perm_f_swap fs)) (rmem_sels vs0 h0))
      (decreases fs)
  =
  let sl0  = gget (vprop_of_list vs0) in
  match fs with
  | []       -> change_equal_slprop (vprop_of_list vs0) (vprop_of_list vs1)
  | f0 :: fs' -> let pfs = Perm.comp_list (L.map (Perm.perm_f_swap #n) fs') in
               let vs' = Perm.apply_perm_r pfs vs0 in
               steel_change_vequiv_aux n vs0 vs' fs' ();
               let sl1' = extract_vars #vs0 #vs' (U.cast (Perm.perm_f (L.length vs0)) pfs)
                                                 (vpl_sels vs0 sl0) in
               steel_change_swap vs' f0;
               Perm.apply_swap_as_rec n f0 vs';
               Perm.apply_r_comp (Perm.perm_f_swap #n f0) pfs vs0;
               change_equal_slprop (vprop_of_list (Perm.list_swap f0 vs'))
                                   (vprop_of_list vs1);
               let sl1  = gget (vprop_of_list vs1) in
               assert (vpl_sels vs1 sl1 === Dl.dlist_swap f0 sl1');
               Dl.apply_swap_as_rec n f0 sl1';
               Dl.apply_r_comp (Perm.perm_f_swap #n f0) pfs (vpl_sels vs0 sl0)

let steel_change_vequiv (#vs0 #vs1 : vprop_list) (#opened:Mem.inames) (f : vequiv vs0 vs1)
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> rmem_sels vs1 h1 == extract_vars f (rmem_sels vs0 h0))
  =
    steel_change_vequiv_aux (L.length vs0) vs0 vs1 (Perm.perm_f_to_swap f) ()


(*** [prog_tree] *)

type pre_t = vprop_list

/// With this definition the shape of post (i.e. the length of the list) must be independant of the returned value
type post_t (a : Type) = Lf.list_fun a vprop'
let post_vp (#a : Type) (post : post_t a) : a -> vprop_list = post.lf_list

type req_t (pre : pre_t) = sl_t pre -> prop
type ens_t (pre : pre_t) (a : Type) (post : post_t a) = sl_t pre -> (x : a) -> sl_t (post_vp post x) -> prop

type repr_steel_t (a : Type)
       (pre : pre_t) (post : post_t a)
       (req : req_t pre) (ens : ens_t pre a post) : Type
  = unit -> Steel a
             (vprop_of_list pre) (fun x -> vprop_of_list (post_vp post x))
             (requires fun h0      -> req (rmem_sels pre h0))
             (ensures  fun h0 x h1 -> ens (rmem_sels pre h0) x (rmem_sels (post_vp post x) h1))

noeq
type prog_tree : (a : Type u#a) -> Type u#(max (a+1) 2) =
  | Tspec  : (a : Type u#a) -> (pre : pre_t) -> (post : post_t a) ->
             (req : req_t pre) -> (ens : ens_t pre a post) ->
             prog_tree a
  | Tret   : (a : Type u#a) -> (x : a) -> prog_tree a
  | Tbind  : (a : Type u#a) -> (b : Type u#a) ->
             (f : prog_tree a) -> (g : a -> prog_tree b) ->
             prog_tree b
  | TbindP : (a : Type u#a) -> (b : Type u#a) ->
             (wp : pure_wp a) -> (x : unit -> PURE a wp) -> (g : a -> prog_tree b) ->
             prog_tree b


(*** slprop unification conditions *)

(* TODO:
   - ? equalities vs vequiv
      + Tspec : post x == post' x @ frame, allow shuffle at the end
   - ~pr ! allow assumptions -> VC
   - ALT: recursively defined type *)

noeq
type tree_cond : (#a : Type u#a) -> (t : prog_tree a) -> (pre : pre_t) -> (post : post_t a) -> Type u#(max (a+1) 2) =
  | TCspec  : (#a : Type u#a) -> (#pre : pre_t) -> (#post : post_t a) -> (#req : req_t pre) -> (#ens : ens_t pre a post) ->
              (pre' : pre_t) -> (post' : post_t a) -> (frame : vprop_list) ->
              (p0 : vequiv pre' L.(pre @ frame)) ->
              (p1 : ((x : a) -> vequiv (post_vp post x @ frame) (post_vp post' x))) ->
              tree_cond (Tspec a pre post req ens) pre' post'
  | TCret   : (#a : Type u#a) -> (#x : a) ->
              (pre : pre_t) -> (post : post_t a) ->
              (p : vequiv pre (post_vp post x)) ->
              tree_cond (Tret a x) pre post
  | TCbind  : (#a : Type u#a) -> (#b : Type u#a) -> (#f : prog_tree a) -> (#g : (a -> prog_tree b)) ->
              (pre : pre_t) -> (itm : post_t a) -> (post : post_t b) ->
              (cf : tree_cond f pre itm) -> (cg : ((x : a) -> tree_cond (g x) (post_vp itm x) post)) ->
              tree_cond (Tbind a b f g) pre post
  | TCbindP : (#a : Type u#a) -> (#b : Type u#a) ->
              (#wp : pure_wp a) -> (#x : (unit -> PURE a wp)) -> (#g : (a -> prog_tree b)) ->
              (pre : pre_t) -> (post : post_t b) ->
              (cg : ((x : a) -> tree_cond (g x) pre post)) ->
              tree_cond (TbindP a b wp x g) pre post

(*** requires / ensures *)

(** return *)

unfold
let return_req (pre : pre_t) : req_t pre
  = fun _ -> True

unfold
let return_ens (#a : Type) (x : a) (p : post_t a) : ens_t (post_vp p x) a p
  = fun sl0 r sl1 ->
      r == x /\ sl1 == sl0

(** bind *)

unfold
let bind_req (#a : Type)
      (#pre : pre_t) (#itm : post_t a)
      (req_f : req_t pre) (ens_f : ens_t pre a itm)
      (req_g : (x:a) -> req_t (post_vp itm x))
  : req_t pre
  = fun sl0 -> req_f sl0 /\
      (forall (x : a) (sl1 : sl_t (post_vp itm x)) .
        ens_f sl0 x sl1 ==> req_g x sl1)

unfold
let bind_ens (#a : Type) (#b : Type)
      (#pre : pre_t) (#itm : post_t a) (#post : post_t b)
      (req_f : req_t pre) (ens_f : ens_t pre a itm)
      (ens_g : (x:a) -> ens_t (post_vp itm x) b post)
  : ens_t pre b post
  = fun sl0 y sl2 ->
      req_f sl0 /\
      (exists (x : a) (sl1 : sl_t (post_vp itm x)) .
        ens_f sl0 x sl1 /\
        ens_g x sl1 y sl2)

(** bind_pure *)

unfold
let bind_pure_req (#a : Type) (wp : pure_wp a)
      (#pre : pre_t)
      (req : a -> req_t pre)
  : req_t pre
  = fun sl0 -> wp (fun x -> req x sl0) /\ True

unfold
let bind_pure_ens (#a : Type) (#b : Type)
      (wp : pure_wp a)
      (#pre : pre_t) (#post : post_t b)
      (ens : a -> ens_t pre b post)
  : ens_t pre b post
  = fun sl0 y sl1 -> as_requires wp /\ (exists (x:a) . as_ensures wp x /\ ens x sl0 y sl1)


(** prog_tree *)

let rec tree_req (#a : Type u#a) (t : prog_tree a)
                 (#pre : pre_t) (#post : post_t a) (c : tree_cond t pre post)
  : Tot (req_t pre) (decreases t) =
  match c with
  | TCspec #_ #pre #_ #req #_  pre' _ frame  p0 _ ->
             (fun sl0 -> req (extract_vars_f pre' pre frame p0 sl0)._1)
  | TCret #_ #_  pre _  _ ->
             return_req pre
  | TCbind #_ #_ #f #g  pre itm _  cf cg ->
             bind_req (tree_req f cf) (tree_ens f cf) (fun x -> tree_req (g x) (cg x))
  | TCbindP #_ #_ #wp #_ #g  pre _  cg ->
             bind_pure_req wp (fun x -> tree_req (g x) (cg x))

and tree_ens (#a : Type u#a) (t : prog_tree a)
             (#pre : pre_t) (#post : post_t a) (c : tree_cond t pre post)
  : Tot (ens_t pre a post) (decreases t) =
  match c with
  | TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1 ->
             (fun sl0' x sl1' ->
                let sl0, frame0 = extract_vars_f pre' pre frame p0 sl0' in
                let sl1, frame1 = extract_vars_f (post_vp post' x) (post_vp post x) frame
                                                 (Perm.pequiv_sym (p1 x)) sl1' in
                frame1 == frame0 /\ ens sl0 x sl1)
  | TCret #a #x  pre post  p ->
             (fun sl0 x' sl1 ->
                x' == x /\
               (let sl0' = extract_vars p sl0 in
                sl1 == sl0'))
  | TCbind #_ #_ #f #g  pre itm post  cf cg ->
             bind_ens (tree_req f cf) (tree_ens f cf) (fun x -> tree_ens (g x) (cg x))
  | TCbindP #_ #_ #wp #_ #g  pre post  cg ->
             bind_pure_ens wp (fun x -> tree_ens (g x) (cg x))


(*** "Monad" *)

/// We define a "monad" (which does not satisfy the monad laws) on a [repr] type which contains a representation
/// of the program as a tree and a corresponding steel function.

noeq
type repr (a : Type) = {
  repr_tree  : prog_tree a;
  repr_steel : (pre : pre_t) -> (post : post_t a) -> (c : tree_cond repr_tree pre post) ->
               repr_steel_t a pre post (tree_req repr_tree c) (tree_ens repr_tree c)
}

let tree_of_steel (#a : Type) (#pre : pre_t) (#post : post_t a) (#req : req_t pre) (#ens : ens_t pre a post)
                  ($f : repr_steel_t a pre post req ens)
  : prog_tree a
  = Tspec a pre post req ens

let repr_of_steel_steel
      (a : Type) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
      (pre' : pre_t) (post' : post_t a) (frame : vprop_list)
      (p0 : vequiv pre' L.(pre @ frame)) (p1 : ((x : a) -> vequiv (post_vp post x @ frame) (post_vp post' x)))
      ($f : repr_steel_t a pre post req ens)
  : (let c = TCspec #a #pre #post #req #ens pre' post' frame p0 p1 in
     repr_steel_t a pre' post' (tree_req _ c) (tree_ens _ c))
  = fun () ->
    (**) steel_change_vequiv p0;
    (**) steel_elim_vprop_of_list_append pre frame;
    let x = f () in
    (**) steel_intro_vprop_of_list_append (post_vp post x) frame;
    (**) let sl1' = gget (vprop_of_list L.(post_vp post x @ frame)) in
    (**) steel_change_vequiv (p1 x);
    (**) let sl1'' = gget (vprop_of_list (post_vp post' x)) in
    (**) assert (vpl_sels (post_vp post' x) sl1''
    (**)      == extract_vars (p1 x) (vpl_sels L.(post_vp post x @ frame) sl1'));
    (**) extract_vars_sym_l (p1 x) (vpl_sels L.(post_vp post x @ frame) sl1');
    Steel.Effect.Atomic.return x

[@@ __tree_reduce__]
let repr_of_steel (#a : Type) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
                  ($f : repr_steel_t a pre post req ens)
  : repr a
  = {
    repr_tree  = tree_of_steel f;
    repr_steel = (fun pre'0 post'0 c ->
                    let (TCspec pre' post' frame  p0 p1) = c in
                    U.cast (repr_steel_t a pre'0 post'0 (tree_req _ c) (tree_ens _ c))
                           (repr_of_steel_steel a pre post req ens pre' post' frame p0 p1 f))
  }


let return_steel
      (a : Type) (x : a)
      (pre : pre_t) (post : post_t a)
      (p : vequiv pre (post_vp post x))
  : (let c = TCret #a #x pre post p in
     repr_steel_t a pre post (tree_req _ c) (tree_ens _ c))
  = fun () ->
    (**) steel_change_vequiv p;
    Steel.Effect.Atomic.return x

[@@ __tree_reduce__]
let return (#a : Type) (x :a)
  : repr a
  = {
    repr_tree  = Tret a x;
    repr_steel = (fun pre0 post0 c ->
        let TCret pre post p = c in
        U.cast (repr_steel_t a pre0 post0 (tree_req _ c) (tree_ens _ c))
               (return_steel a x pre post p))
  }


let elim_tree_req_bind (#a #b : Type) (f : prog_tree a) (g : a -> prog_tree b)
      (#pre : pre_t) (#post : post_t b) (#itm : post_t a)
      (cf  : tree_cond f pre itm) (cg : (x:a) -> tree_cond (g x) (post_vp itm x) post)
      (sl0 : t_of (vprop_of_list pre))
  : Lemma (requires tree_req _ (TCbind #a #b #f #g pre itm post cf cg) (vpl_sels pre sl0))
          (ensures  tree_req f cf (vpl_sels pre sl0) /\
                    (forall (x : a) (sl1 : t_of (vprop_of_list (post_vp itm x))) .
                      tree_ens f cf (vpl_sels pre sl0) x (vpl_sels (post_vp itm x) sl1) ==>
                      tree_req (g x) (cg x) (vpl_sels (post_vp itm x) sl1)))
  = assert_norm (tree_req _ (TCbind #a #b #f #g pre itm post cf cg) (vpl_sels pre sl0) == (
      tree_req f cf (vpl_sels pre sl0) /\
      (forall (x : a) (sl1 : sl_t (post_vp itm x)) .
         tree_ens f cf (vpl_sels pre sl0) x sl1 ==> tree_req (g x) (cg x) sl1)
    ))

let intro_tree_ens_bind (#a #b : Type) (f : prog_tree a) (g : a -> prog_tree b)
      (#pre : pre_t) (#post : post_t b) (#itm : post_t a)
      (cf  : tree_cond f pre itm) (cg : (x:a) -> tree_cond (g x) (post_vp itm x) post)
      (sl0 : t_of (vprop_of_list pre)) (x : a) (sl1 : t_of (vprop_of_list (post_vp itm x)))
      (y : b) (sl2 : t_of (vprop_of_list (post_vp post y)))
  : Lemma (requires tree_req f cf (vpl_sels pre sl0) /\
                    tree_ens f cf (vpl_sels pre sl0) x (vpl_sels (post_vp itm x) sl1) /\
                    tree_ens (g x) (cg x) (vpl_sels (post_vp itm x) sl1) y (vpl_sels (post_vp post y) sl2))
          (ensures  tree_ens _ (TCbind #a #b #f #g pre itm post cf cg)
                             (vpl_sels pre sl0) y (vpl_sels (post_vp post y) sl2))
  = assert_norm (tree_ens _ (TCbind #a #b #f #g pre itm post cf cg)
                          (vpl_sels pre sl0) y (vpl_sels (post_vp post y) sl2) == (
      tree_req f cf (vpl_sels pre sl0) /\
        (exists (x : a) (sl1 : sl_t (post_vp itm x)) .
          tree_ens f cf (vpl_sels pre sl0) x sl1 /\
          tree_ens (g x) (cg x) sl1 y (vpl_sels (post_vp post y) sl2))
    ))

let bind_steel
      (a : Type) (b : Type) (f : prog_tree a) (g : (a -> prog_tree b))
      (pre : pre_t) (itm : post_t a) (post : post_t b)
      (cf : tree_cond f pre itm) (cg : ((x : a) -> tree_cond (g x) (post_vp itm x) post))
      ($rf : repr_steel_t a pre itm (tree_req f cf) (tree_ens f cf))
      ($rg : (x : a) -> repr_steel_t b (post_vp itm x) post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbind #a #b #f #g pre itm post cf cg in
     repr_steel_t b pre post (tree_req _ c) (tree_ens _ c))
  = fun () ->
    (**) let sl0 = gget (vprop_of_list pre) in
    (**) elim_tree_req_bind f g cf cg sl0;
    let x = rf () in
    (**) let sl1 = gget (vprop_of_list (post_vp itm x)) in
    let y = rg x () in
    (**) let sl2 = gget (vprop_of_list (post_vp post y)) in
    (**) intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2;
    Steel.Effect.Atomic.return y

[@@ __tree_reduce__]
let bind (#a #b : Type)
      (f : repr a) (g : a -> repr b)
  : repr b
  = {
    repr_tree  = Tbind a b f.repr_tree (fun x -> (g x).repr_tree);
    repr_steel = (fun pre0 post0 c ->
                    let (TCbind #a' #b' #tf #tg pre itm post cf cg) = c in
                    let rg (x : a) : repr_steel_t b (post_vp itm x) post _ _
                                   = (g x).repr_steel _ _ (cg x) in
                    U.cast (repr_steel_t b pre0 post0 (tree_req _ c) (tree_ens _ c))
                           (bind_steel a b tf tg pre itm post cf cg (f.repr_steel _ _ cf) rg))
  }

(* --------------------------- *)

open Steel.FractionalPermission
open Steel.Reference

unfold
let read_pre  (r : ref nat) : pre_t
  = [vptr' r full_perm]
unfold
let read_post (r : ref nat) : post_t nat
  = Lf.const nat [vptr' r full_perm]
let read_req  (r : ref nat) : req_t (read_pre r)
  = fun sl0 -> True
let read_ens  (r : ref nat) : ens_t (read_pre r) nat (read_post r)
  = fun sl0 x sl1 ->
    assert (L.length (vprop_list_sels_t (post_vp (read_post r) x)) == 1)
      by T.(trefl ());
    Dl.index sl1 0 == Dl.index sl0 0 /\ x == Dl.index sl0 0

let steel_read0 (r : ref nat) () :
  Steel nat (vprop_of_list [vptr' r full_perm]) (fun _ -> vprop_of_list [vptr' r full_perm])
    (requires fun _ -> True)
    (ensures fun h0 x h1 -> let sl0 = rmem_sels [vptr' r full_perm] h0 in
                         let sl1 = rmem_sels [vptr' r full_perm] h1 in
                         Dl.index sl1 0 == Dl.index sl0 0 /\ x == Dl.index sl0 0)
  =
    (**) change_equal_slprop (vprop_of_list [vptr' r full_perm]) (vptr r `star` emp);
    let x = read r in
    (**) change_equal_slprop (vptr r `star` emp) (vprop_of_list [vptr' r full_perm]);
    Steel.Effect.Atomic.return x

let steel_read (r : ref nat)
  : repr_steel_t nat (read_pre r) (read_post r) (read_req r) (read_ens r)
  = U.cast_by (repr_steel_t nat (read_pre r) (read_post r) (read_req r) (read_ens r))
            (steel_read0 r)
            (_ by T.(trefl ()))

unfold let r_read (r : ref nat) : repr nat =
  repr_of_steel (read_pre r) (read_post r) (read_req r) (read_ens r) (steel_read r)

unfold
let test_M (r : ref nat) : repr nat =
  x <-- r_read r;
  return x

irreducible
let print_util (#a : Type) (x : a) : prop = True

let normal_tree_steps : list norm_step = [
    delta_attr [`%__tree_reduce__];
    delta_qualifier ["unfold"];
    delta_only [`%Mkrepr?.repr_tree];
    iota; zeta
  ]

let normal_spec_steps : list norm_step = [
    delta; iota; zeta; primops
  ]

let normal_read_vp : list norm_step = [
    delta_only [`%read_pre; `%read_post; `%post_vp; `%L.map; `%L.append; `%L.op_At; `%U.app_on];
    iota; zeta_full
  ]

//let _ = fun r ->
//  assert (print_util (test r).repr_tree) by T.(norm normal_tree_steps; qed ())

let test_equiv (r : ref nat) : vequiv ([vptr' r full_perm]) [vptr' r full_perm] =
  Perm.id_n 1

unfold
let test_cond (r : ref nat)
  : tree_cond (test_M r).repr_tree [vptr' r full_perm] (Lf.const nat [vptr' r full_perm])
  = _ by T.(
    apply (`TCbind);
     (apply (`(TCspec _ (read_post (`@r)) []));
       (norm normal_read_vp; exact (`test_equiv (`@r)));
       (let x = intro () in
        norm normal_read_vp; (* TODO: @ is not unfolded *)
        exact (`test_equiv (`@r))));
     (let x = intro () in
      apply (`TCret);
       (norm normal_read_vp; exact (`test_equiv (`@r))));
  qed ())

//let _ = fun r ->
//  assert (print_util (tree_req (test r).repr_tree (test_cond r)))
//    by T.(norm normal_spec_steps; qed ())

(*
(* --------------------------- *)

/// generating a non-deterministic function representing the program tree

module ND = Learn.Effect.NonDeterminism

let cast_nd (#a #b : Type) (#req0 : a -> ND.req_t) (#ens0 : (x:a) -> ND.ens_t b (req0 x))
                           (req1  : a -> ND.req_t) (ens1  : (x:a) -> ND.ens_t b (req1 x))
                           ($f : (x : a) -> ND.ND b (req0 x) (ens0 x))
  : Pure ((x : a) -> ND.ND b (req1 x) (ens1 x))
         (requires forall (x : a) . ND.subcomp_pre (req0 x) (ens0 x) (req1 x) (ens1 x))
         (ensures fun _ -> True)
  = fun x -> f x

[@@ __tree_reduce__]
let rec prog_tree_to_ND (#a : Type) (p : prog_tree a)
  : (sl0 : sl_t) -> ND.ND (a & sl_t) (requires tree_req p sl0) (ensures fun (x, sl1) -> tree_ens p sl0 x sl1)
  = match p with
  | Tspec a req ens   -> (fun sl0 -> ND.most_general (a&sl_t) (req sl0) (fun (x, sl1) -> ens sl0 x sl1))
  | Tret  a x         -> (fun sl0 -> ND.return (x, sl0))
  | Tbind a b f g     -> FStar.Classical.forall_intro (FStar.Classical.move_requires
                          (elim_tree_req_bind f (fun x -> (g x)))); 
                        introduce forall sl0 (x : a) sl1 (y : b) sl2.
                          tree_req f sl0 /\ tree_ens f sl0 x sl1 /\ tree_ens (g x) sl1 y sl2 ==>
                          tree_ens (Tbind a b f g) sl0 y sl2
                          with introduce _ ==> _
                          with _ . intro_tree_ens_bind f (fun x -> (g x)) sl0 x sl1 y sl2;
                        (fun sl0 -> let (x, sl1) = prog_tree_to_ND f sl0 in
                                 prog_tree_to_ND (g x) sl1)
  | TbindP a b wp x g -> FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
                        let req sl0 : ND.req_t =
                          ND.bind_pure_nstate_req wp (fun xv -> tree_req (g xv) sl0) in
                        let ens sl0 : ND.ens_t (b & sl_t) (req sl0) =
                          ND.bind_pure_nstate_ens wp
                               (fun xv -> tree_req (g xv) sl0)
                               (fun xv (y, sl1) -> tree_ens (g xv) sl0 y sl1) in
                        let rt (sl0 : sl_t) :
                          ND.ND (b & sl_t)
                            (requires req sl0)
                            (ensures  ens sl0)
                          = prog_tree_to_ND (g (x ())) sl0
                        in
                        let req' sl0 : ND.req_t = tree_req (TbindP a b wp x g) sl0 in
                        let ens' sl0 : ND.ens_t (b & sl_t) (req' sl0) =
                          fun (y, sl1) -> tree_ens (TbindP a b wp x g) sl0 y sl1 in
                        assert (forall (sl0 : sl_t) . ND.subcomp_pre (req sl0) (ens sl0) (req' sl0) (ens' sl0))
                          by T.(let _ = forall_intro () in
                                let _ = implies_intro () in
                                smt ());
                        cast_nd req' ens' rt

let normal_tree_ND_steps : list norm_step = [
    delta_attr [`%__tree_reduce__];
    delta_qualifier ["unfold"];
    delta_only [`%Mkrepr?.repr_tree; `%tree_of_steel];
    iota; zeta_full
  ]

(*
let _ = assert (print_util (prog_tree_to_ND (test.repr_tree)))
          by T.(norm (normal_tree_ND_steps); qed ())
*)
*)