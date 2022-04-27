module Experiment.Steel.Repr.M

module T    = FStar.Tactics
module U    = Learn.Util
module L    = FStar.List.Pure
module Uv   = FStar.Universe
module Ll   = Learn.List
module Mem  = Steel.Memory
module Perm = Learn.Permutation
module FExt = FStar.FunctionalExtensionality

open FStar.Calc
open FStar.Classical.Sugar

open Steel.Effect
open Steel.Effect.Atomic

#set-options "--ide_id_info_off"

irreducible let __tree_reduce__ : unit = ()

(** [var_list] *)

(* ALT? dependent arrrow Fin.fin n -> _ *)

type ty_list = list Type

noeq
type var_list : ty_list -> Type =
  | VLNil : var_list []
  | VLCons : (t0 : Type) -> (x0 : t0) ->
             (ts : ty_list) -> (xs : var_list ts) ->
             var_list (t0 :: ts)

let rec var_at (#ts : ty_list) (xs : var_list ts) (i : nat{i < L.length ts})
  : L.index ts i
  = let VLCons t0 x0 ts1 xs1 = xs in
    if i = 0 then x0
    else U.cast (L.index ts i) (var_at xs1 (i-1))

let rec var_list_extensionality (#ts : ty_list) (xs ys : var_list ts)
  : Lemma (requires forall (i : nat {i < L.length ts}) . var_at xs i == var_at ys i)
          (ensures xs == ys)
          (decreases ts)
  = match ts with
    | [] -> ()
    | t0 :: ts' -> let VLCons _ x _ xs' = xs in
                let VLCons _ y _ ys' = ys in
                assert (x == var_at xs 0);
                assert (y == var_at ys 0);
                introduce forall (i : nat {i < L.length ts'}) . var_at xs' i == var_at ys' i
                  with (assert (var_at xs' i === var_at xs (i+1));
                        assert (var_at ys' i === var_at ys (i+1)));
                var_list_extensionality #ts' xs' ys'

let rec var_splitAt (n : nat) (#ts : ty_list) (xs : var_list ts)
  : Tot (var_list (L.splitAt n ts)._1 & var_list (L.splitAt n ts)._2)
        (decreases n)
  = if n = 0 then VLNil, xs
    else match xs with
    | VLNil              -> VLNil, VLNil
    | VLCons t0 x0 ts xs -> let xs0, xs1 = var_splitAt (n-1) xs in
                           VLCons t0 x0 _ xs0, xs1

let rec var_initi (lb ub : nat)
          (t : (i:nat{lb <= i /\ i < ub}) -> Tot Type)
          (f : (i:nat{lb <= i /\ i < ub}) -> Tot (t i))
  : Tot (var_list (Ll.initi lb ub t)) (decreases ub - lb)
  = if lb < ub then VLCons (t lb) (f lb) _ (var_initi (lb + 1) ub t f) else VLNil

let rec var_initi_at (lb ub : nat)
          (t : (i:nat{lb <= i /\ i < ub}) -> Tot Type)
          (f : (i:nat{lb <= i /\ i < ub}) -> Tot (t i))
          (i : nat {i < L.length (Ll.initi lb ub t)})
  : Lemma (ensures var_at (var_initi lb ub t f) i == f (lb+i)) (decreases i)
          [SMTPat (var_at (var_initi lb ub t f) i)]
  = if i = 0 then () else var_initi_at (lb+1) ub t f (i-1)

let var_apply_perm_r (#n : nat) (p : Perm.perm_f n) (#ts : ty_list {L.length ts == n}) (xs : var_list ts)
  : var_list (Perm.apply_perm_r p ts)
  = var_initi 0 n (fun i -> L.index ts (p i)) (fun i -> var_at xs (p i))

let var_apply_r_id_n (len : nat) (#ts : ty_list{L.length ts = len}) (xs :var_list ts)
  : Lemma (var_apply_perm_r (Perm.id_n len) xs == xs) [SMTPat (var_apply_perm_r (Perm.id_n len) xs)]
  = var_list_extensionality (var_apply_perm_r (Perm.id_n len) xs) xs

let var_apply_r_comp (#len : nat) (f g : Perm.perm_f len) (#ts : ty_list {L.length ts == len}) (xs : var_list ts)
  : Lemma (var_apply_perm_r (f `Perm.comp` g) xs === var_apply_perm_r f (var_apply_perm_r g xs))
  = Perm.apply_r_comp f g ts;
    var_list_extensionality (var_apply_perm_r (f `Perm.comp` g) xs) (var_apply_perm_r f (var_apply_perm_r g xs))

let rec var_list_swap (i : nat) (#ts : ty_list{i <= L.length ts - 2}) (xs : var_list ts)
  : Tot (var_list (Perm.list_swap i ts)) (decreases i)
  = if i = 0
    then let VLCons tx x _ (VLCons ty y _ tl) = xs in
         VLCons ty y _ (VLCons tx x _ tl)
    else let VLCons tx x ts tl = xs in
         VLCons tx x _ (var_list_swap (i-1) tl)

#push-options "--z3rlimit 20"
let var_apply_perm_f_shift (#len : nat) (p : Perm.perm_f len)
      (#hd_ty : Type) (#tl_ty : ty_list {L.length tl_ty = len})
      (hd : hd_ty) (tl : var_list tl_ty)
  : Lemma (var_apply_perm_r (Perm.perm_f_shift p) (VLCons _ hd _ tl)
       === VLCons _ hd _ (var_apply_perm_r p tl))
  = Perm.apply_perm_f_shift p hd_ty tl_ty;
    var_list_extensionality
      (var_apply_perm_r (Perm.perm_f_shift p) (VLCons _ hd _ tl))
      (VLCons _ hd _ (var_apply_perm_r p tl))
#pop-options

#push-options "--z3rlimit 60"
let rec var_apply_swap_as_rec (len : nat) (i : nat {i <= len-2})
          (#ts : ty_list {L.length ts = len}) (xs : var_list ts)
  : Lemma (ensures var_apply_perm_r (Perm.perm_f_swap #len i) xs === var_list_swap i xs)
          (decreases len)
  = Perm.apply_swap_as_rec len i ts;
    if i = 0 then begin
       let VLCons _ x _ (VLCons _ y _ tl) = xs in
       var_list_extensionality
         (var_apply_perm_r (Perm.perm_f_swap #len 0) (VLCons _ x _ (VLCons _ y _ tl)))
         (VLCons _ y _ (VLCons _ x _ tl))
    end else begin
      let VLCons _ hd _ tl = xs in
      Perm.perm_f_swap_rec_rel (len-1) (i-1);
      var_apply_perm_f_shift (Perm.perm_f_swap #(len-1) (i-1)) hd tl;
      var_apply_swap_as_rec (len-1) (i-1) tl
    end
#pop-options


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


let vprop_list_sels_t : vprop_list -> ty_list =
  L.map (fun (vp:vprop') -> vp.t) 

unfold
let sl_t (vs : vprop_list) : Type = var_list (vprop_list_sels_t vs)

let vprop_list_sels_t_eq (vs : vprop_list) (i : nat {i < L.length vs})
  : Lemma (ensures L.index (vprop_list_sels_t vs) i == (L.index vs i).t)
          [SMTPat (L.index (vprop_list_sels_t vs) i)]
  = Ll.map_index (fun (vp:vprop') -> vp.t) vs i

let rec vpl_sels (vs : vprop_list) (sl : t_of (vprop_of_list vs))
  : Tot (sl_t vs) (decreases vs)
  = match (|vs, sl|) <: (vs : vprop_list & t_of (vprop_of_list vs))  with
  | (|[], _|) -> VLNil
  | (|v0 :: vs, (x0, xs)|) -> VLCons v0.t x0 _ (vpl_sels vs xs)

unfold
let rmem_sels (#p:vprop) (vs : vprop_list)
    (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (vprop_of_list vs) /\ True)})
  : GTot (sl_t vs)
  = vpl_sels vs (h (vprop_of_list vs))

(*
let rec rmem_sels (vs : vprop_list) (h : rmem (vprop_of_list vs))
  : GTot (var_list (vprop_list_sels_t vs)) (decreases vs)
  = match vs with
  | []     -> VLNil
  | v :: vs -> let _ : (can_be_split (vprop_of_list (v :: vs)) (VUnit v) /\ True) = _
                 by (T.norm [iota; zeta; delta_only [`%vprop_of_list]]; selector_tactic ()) in
              let _ : (can_be_split (vprop_of_list (v :: vs)) (vprop_of_list vs) /\ True) = _
                 by (T.norm [iota; zeta; delta_only [`%vprop_of_list]]; selector_tactic ()) in
              VLCons v.t (h (VUnit v)) _ (rmem_sels vs (focus_rmem h (vprop_of_list vs)))

let focus_rmem_feq (p q r : vprop) (h : rmem p)
  : Lemma (requires can_be_split p q /\ can_be_split q r)
          (ensures  can_be_split p r /\ focus_rmem h q r == h r)
  = can_be_split_trans p q r

let rec rmem_sels_eq (vs : vprop_list) (h : rmem (vprop_of_list vs)) (i : nat {i < L.length vs})
  : Lemma (ensures vprop_of_list_can_be_split vs i;
                  (var_at (rmem_sels vs h) i == h (VUnit (L.index vs i))))
  = let v :: vs' = vs in
    if i = 0 then ()
    else begin
      let _ : (can_be_split (vprop_of_list (v :: vs')) (vprop_of_list vs') /\ True) = _
         by (T.norm [iota; zeta; delta_only [`%vprop_of_list]]; selector_tactic ()) in
      U.f_equal (fun vs -> rmem (vprop_of_list vs)) vs (v :: vs');
      vprop_of_list_can_be_split vs' (i-1);
      focus_rmem_feq (vprop_of_list (v :: vs')) (vprop_of_list vs') (VUnit (L.index vs' (i-1)))
                     (U.cast (rmem (vprop_of_list (v :: vs'))) h);
      rmem_sels_eq vs' (focus_rmem h (vprop_of_list vs')) (i-1)
  end
*)

unfold
let split_vars (vs0 vs1 : vprop_list) (xs : sl_t (vs0@vs1))
  : sl_t vs0 & sl_t vs1
  =
    Ll.map_append (fun (vp:vprop') -> vp.t) vs0 vs1;
    L.lemma_append_splitAt (vprop_list_sels_t vs0) (vprop_list_sels_t vs1);
    var_splitAt (L.length vs0) xs
 

let rec steel_elim_vprop_of_list_append #opened (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list L.(vs0@vs1)) (fun () -> vprop_of_list vs0 `star` vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> split_vars vs0 vs1 (rmem_sels (vs0@vs1) h0) == (rmem_sels vs0 h1, rmem_sels vs1 h1))
      (decreases vs0)
  = match vs0 with
    | [] -> change_equal_slprop (vprop_of_list L.(vs0@vs1)) (vprop_of_list vs1);
           change_equal_slprop emp (vprop_of_list vs0)
    | v0 :: vs0' ->
           change_equal_slprop (vprop_of_list L.(vs0@vs1)) (VUnit v0 `star` vprop_of_list L.(vs0'@vs1));
           steel_elim_vprop_of_list_append vs0' vs1;
           change_equal_slprop (VUnit v0 `star` vprop_of_list vs0') (vprop_of_list (vs0))

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
           steel_intro_vprop_of_list_append vs0' vs1;
           change_equal_slprop (VUnit v0 `star` vprop_of_list L.(vs0'@vs1)) (vprop_of_list L.(vs0@vs1))
           

(** [vequiv] *)

let vequiv (vs0 vs1 : vprop_list) : Type
  = f : Perm.perm_f (L.length vs0) {vs1 == Perm.apply_perm_r f vs0}

let vequiv_sels_t (#vs0 #vs1 : vprop_list) (f : vequiv vs0 vs1)
  : Lemma (vprop_list_sels_t vs1 == Perm.apply_perm_r f (vprop_list_sels_t vs0))
  = Perm.map_apply_r f (fun (vp:vprop') -> vp.t) vs0

unfold
let extract_vars (#src #dst : vprop_list)
                 (p : vequiv src dst)
                 (xs : sl_t src)
  : sl_t dst
  =
    vequiv_sels_t p;
    var_apply_perm_r p xs

unfold
let extract_vars_f (src dst frame : vprop_list)
                   (p : vequiv src L.(dst@frame))
                   (xs : sl_t src)
  : sl_t dst & sl_t frame
  =
    split_vars dst frame (extract_vars p xs)

unfold
let vequiv_sym (#vs0 #vs1 : vprop_list) (f : vequiv vs0 vs1) : vequiv vs1 vs0
  = 
    Perm.(calc (==) {
      apply_perm_r (inv_f f) vs1;
    == {}
      apply_perm_r (inv_f f) (apply_perm_r f vs0);
    == {apply_r_comp (inv_f f) f vs0}
      vs0;
    });
    U.cast #(Perm.perm_f (L.length vs0)) (Perm.perm_f (L.length vs1)) (Perm.inv_f f)

let extract_vars_sym_l (#vs0 #vs1 : vprop_list) (f : vequiv vs0 vs1) (xs : sl_t vs0)
  : Lemma (extract_vars (vequiv_sym f) (extract_vars f xs) == xs)
  =
    vequiv_sels_t f; vequiv_sels_t (vequiv_sym f);
    calc (==) {
      extract_vars (vequiv_sym f) (extract_vars f xs);
    == {}
      var_apply_perm_r (vequiv_sym f) (var_apply_perm_r f xs);
    == {}
      var_apply_perm_r (Perm.inv_f f) (var_apply_perm_r f xs);
    == {var_apply_r_comp #(L.length vs0) (Perm.inv_f f) f xs}
      xs;
    }

/// applying a permutation on the context's vprop

let rec steel_change_swap (#opened:Mem.inames)
          (vs0 : vprop_list) (i : nat {i <= L.length vs0 - 2})
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list (Perm.list_swap i vs0))
      (requires fun _ -> True) (ensures fun h0 () h1 ->
        rmem_sels (Perm.list_swap i vs0) h1 === var_list_swap i (rmem_sels vs0 h0))
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
               assert (vpl_sels vs1 sl1 === var_list_swap f0 sl1');
               var_apply_swap_as_rec n f0 sl1';
               var_apply_r_comp (Perm.perm_f_swap #n f0) pfs (vpl_sels vs0 sl0)

let steel_change_vequiv (#vs0 #vs1 : vprop_list) (#opened:Mem.inames) (f : vequiv vs0 vs1)
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> rmem_sels vs1 h1 == extract_vars f (rmem_sels vs0 h0))
  =
    steel_change_vequiv_aux (L.length vs0) vs0 vs1 (Perm.perm_f_to_swap f) ()


(*** [prog_tree] *)

let pre_t = vprop_list
let post_t (a : Type) = a -> vprop_list
type req_t (pre : pre_t) = sl_t pre -> prop
type ens_t (pre : pre_t) (a : Type) (post : post_t a) = sl_t pre -> (x : a) -> sl_t (post x) -> prop

type repr_steel_t (a : Type)
       (pre : pre_t) (post : post_t a)
       (req : req_t pre) (ens : ens_t pre a post) : Type
  = unit -> Steel a
             (vprop_of_list pre) (fun x -> vprop_of_list (post x))
             (requires fun h0      -> req (rmem_sels pre h0))
             (ensures  fun h0 x h1 -> ens (rmem_sels pre h0) x (rmem_sels (post x) h1))

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
   - ALT: datatype indexed by t *)

let rec tree_cond (#a : Type u#a ) (t : prog_tree a) (pre : pre_t) (post : post_t a)
  : Tot (Type u#(max a 2)) (decreases t)
  = match t with
  | Tspec a pre' post' _ _ ->
          frame : vprop_list & vequiv pre L.(pre' @ frame)
                             & ((x:a) -> vequiv (post' x @ frame) (post x))
  | Tret  a x ->
          Uv.raise_t u#0 u#(max a 2) (vequiv pre (post x))
  | Tbind a b f g ->
          itm : (a -> vprop_list) & tree_cond f pre itm & ((x:a) -> tree_cond (g x) (itm x) post)
  | TbindP a b _ _ g ->
          (x:a) -> tree_cond (g x) pre post

(*** requires / ensures *)

(** return *)

unfold
let return_req (pre : pre_t) : req_t pre
  = fun _ -> True

unfold
let return_ens (#a : Type) (x : a) (p : a -> vprop_list) : ens_t (p x) a p
  = fun sl0 r sl1 ->
      r == x /\ sl1 == sl0

(** bind *)

unfold
let bind_req (#a : Type)
      (#pre : pre_t) (#itm : a -> vprop_list)
      (req_f : req_t pre) (ens_f : ens_t pre a itm)
      (req_g : (x:a) -> req_t (itm x))
  : req_t pre
  = fun sl0 -> req_f sl0 /\
      (forall (x : a) (sl1 : sl_t (itm x)) .
        ens_f sl0 x sl1 ==> req_g x sl1)

unfold
let bind_ens (#a : Type) (#b : Type)
      (#pre : pre_t) (#itm : a -> vprop_list) (#post : post_t b)
      (req_f : req_t pre) (ens_f : ens_t pre a itm)
      (ens_g : (x:a) -> ens_t (itm x) b post)
  : ens_t pre b post
  = fun sl0 y sl2 ->
      req_f sl0 /\
      (exists (x : a) (sl1 : sl_t (itm x)) .
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
  let tc : (t : prog_tree a & tree_cond t pre post) = (|t, c|) in
  match tc with
  | (|Tspec  _ pre' _ req _, (|frame, p0, _|)|) ->
             (fun sl0 -> req (extract_vars_f pre pre' frame p0 sl0)._1)
  | (|Tret   _ _, _|) ->
             return_req pre
  | (|Tbind  _ _ f g, (|itm, cf, cg|)|) ->
             bind_req (tree_req f cf) (tree_ens f cf) (fun x -> tree_req (g x) (cg x))
  | (|TbindP _ _ wp _ g, cg|) ->
             bind_pure_req wp (fun x -> tree_req (g x) (cg x))

and tree_ens (#a : Type u#a) (t : prog_tree a)
             (#pre : pre_t) (#post : post_t a) (c : tree_cond t pre post)
  : Tot (ens_t pre a post) (decreases t) =
  let tc : (t : prog_tree a & tree_cond t pre post) = (|t, c|) in
  match tc with
  | (|Tspec  a pre' post' req ens, (|frame, p0, p1|)|) ->
             (fun sl0 x sl1 ->
                let sl0', frame0 = extract_vars_f pre  pre'  frame p0 sl0 in
                let sl1', frame1 = extract_vars_f (post x) (post' x) frame (vequiv_sym (p1 x)) sl1 in
                frame1 == frame0 /\ ens sl0' x sl1')
  | (|Tret   _ x, p|) ->
             (fun sl0 x' sl1 ->
                x' == x /\
               (let sl0' = extract_vars #pre #(post x) (Uv.downgrade_val u#0 u#(max a 2) p) sl0 in
                sl1 == sl0'))
  | (|Tbind  _ _ f g, (|itm, cf, cg|)|) ->
             bind_ens (tree_req f cf) (tree_ens f cf) (fun x -> tree_ens (g x) (cg x))
  | (|TbindP _ _ wp _ g, cg|) ->
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


[@@ __tree_reduce__]
let repr_of_steel (#a : Type) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
                  ($f : repr_steel_t a pre post req ens)
  : repr a
  = {
    repr_tree  = tree_of_steel f;
    repr_steel = (fun pre' post' (|frame, p0, p1|) () ->
        (**) steel_change_vequiv p0;
        (**) steel_elim_vprop_of_list_append pre frame;
        let x = f () in
        (**) steel_intro_vprop_of_list_append (post x) frame;
        (**) let sl1' = gget (vprop_of_list L.(post x @ frame)) in
        (**) steel_change_vequiv (p1 x);
        (**) let sl1'' = gget (vprop_of_list (post' x)) in
        (**) assert (vpl_sels (post' x) sl1'' == extract_vars (p1 x) (vpl_sels L.(post x @ frame) sl1'));
        (**) extract_vars_sym_l (p1 x) (vpl_sels L.(post x @ frame) sl1');
        return x)
  }

[@@ __tree_reduce__]
let return (#a : Type) (x :a)
  : repr a
  = {
    repr_tree  = Tret a x;
    repr_steel = (fun pre post p () ->
        (**) steel_change_vequiv (Uv.downgrade_val p);
        Steel.Effect.Atomic.return x)
  }


let elim_tree_req_bind (#a #b : Type) (f : prog_tree a) (g : a -> prog_tree b)
      (#pre : pre_t) (#post : post_t b) (#itm : a -> vprop_list)
      (cf  : tree_cond f pre itm) (cg : (x:a) -> tree_cond (g x) (itm x) post)
      (sl0 : t_of (vprop_of_list pre))
  : Lemma (requires tree_req (Tbind a b f g) (|itm, cf, cg|) (vpl_sels pre sl0))
          (ensures  tree_req f cf (vpl_sels pre sl0) /\
                    (forall (x : a) (sl1 : t_of (vprop_of_list (itm x))) .
                      tree_ens f cf (vpl_sels pre sl0) x (vpl_sels (itm x) sl1) ==>
                      tree_req (g x) (cg x) (vpl_sels (itm x) sl1)))
  = assert_norm (tree_req (Tbind a b f g) (|itm, cf, cg|) (vpl_sels pre sl0) == (
      tree_req f cf (vpl_sels pre sl0) /\
      (forall (x : a) (sl1 : sl_t (itm x)) .
         tree_ens f cf (vpl_sels pre sl0) x sl1 ==> tree_req (g x) (cg x) sl1)
    ))

let intro_tree_ens_bind (#a #b : Type) (f : prog_tree a) (g : a -> prog_tree b)
      (#pre : pre_t) (#post : post_t b) (#itm : a -> vprop_list)
      (cf  : tree_cond f pre itm) (cg : (x:a) -> tree_cond (g x) (itm x) post)
      (sl0 : t_of (vprop_of_list pre)) (x : a) (sl1 : t_of (vprop_of_list (itm x)))
      (y : b) (sl2 : t_of (vprop_of_list (post y)))
  : Lemma (requires tree_req f cf (vpl_sels pre sl0) /\
                    tree_ens f cf (vpl_sels pre sl0) x (vpl_sels (itm x) sl1) /\
                    tree_ens (g x) (cg x) (vpl_sels (itm x) sl1) y (vpl_sels (post y) sl2))
          (ensures  tree_ens (Tbind a b f g) #pre #post (|itm, cf, cg|)
                             (vpl_sels pre sl0) y (vpl_sels (post y) sl2))
  = assert_norm (tree_ens (Tbind a b f g) #pre #post (|itm, cf, cg|)
                          (vpl_sels pre sl0) y (vpl_sels (post y) sl2) == (
      tree_req f cf (vpl_sels pre sl0) /\
        (exists (x : a) (sl1 : sl_t (itm x)) .
          tree_ens f cf (vpl_sels pre sl0) x sl1 /\
          tree_ens (g x) (cg x) sl1 y (vpl_sels (post y) sl2))
    ))

[@@ __tree_reduce__]
let bind (#a #b : Type)
      (f : repr a) (g : a -> repr b)
  : repr b
  = {
    repr_tree  = Tbind a b f.repr_tree (fun x -> (g x).repr_tree);
    repr_steel = (fun pre post (|itm, cf, cg|) () ->
        (**) let sl0 = gget (vprop_of_list pre) in
        (**) assert (tree_req (Tbind a b f.repr_tree (fun x -> (g x).repr_tree))
        (**)                  (|itm, cf, cg|) (vpl_sels pre sl0));
        (**) elim_tree_req_bind f.repr_tree (fun x -> (g x).repr_tree) cf cg sl0;
        let x = f.repr_steel pre itm cf () in
        (**) let sl1 = gget (vprop_of_list (itm x)) in
        (**) assert (tree_ens f.repr_tree cf (vpl_sels pre sl0) x (vpl_sels (itm x) sl1));
        (**) assert (tree_req (g x).repr_tree (cg x) (vpl_sels (itm x) sl1));
        let y = (g x).repr_steel (itm x) post (cg x) () in
        (**) let sl2 = gget (vprop_of_list (post y)) in
        (**) intro_tree_ens_bind f.repr_tree (fun x -> (g x).repr_tree) cf cg
        (**)                     sl0 x sl1 y sl2;
        Steel.Effect.Atomic.return y)
  }

(* --------------------------- *)

open Steel.FractionalPermission
open Steel.Reference

unfold
let read_pre  (r : ref nat) : pre_t
  = [vptr' r full_perm]
unfold
let read_post (r : ref nat) : post_t nat
  = fun _ -> [vptr' r full_perm]
let read_req  (r : ref nat) : req_t (read_pre r)
  = fun sl0 -> True
let read_ens  (r : ref nat) : ens_t (read_pre r) nat (read_post r)
  = fun sl0 x sl1 -> var_at sl1 0 == var_at sl0 0 /\ x == var_at sl0 0

let steel_read (r : ref nat)
  : repr_steel_t nat (read_pre r) (read_post r) (read_req r) (read_ens r)
  = fun () -> (**) change_equal_slprop (vprop_of_list (read_pre r)) (vptr r `star` emp);
           let x = read r in
           (**) change_equal_slprop (vptr r `star` emp) (vprop_of_list (read_post r x));
           Steel.Effect.Atomic.return x

unfold let r_read (r : ref nat) : repr nat =
  repr_of_steel (read_pre r) (read_post r) (read_req r) (read_ens r) (steel_read r)

unfold
let test (r : ref nat) : repr nat =
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

let normal_tree_cond_steps : list norm_step = [
    delta_attr [`%__tree_reduce__];
    delta_qualifier ["unfold"];
    delta_only [`%Mkrepr?.repr_tree; `%tree_cond; `%tree_of_steel];
    iota; zeta
  ]

let normal_spec_steps : list norm_step = [
    delta; iota; zeta; primops
  ]


//let _ = fun r ->
//  assert (print_util (test r).repr_tree) by T.(norm normal_tree_steps; qed ())

unfold
let test_cond (r : ref nat)
  : norm normal_tree_cond_steps (tree_cond (test r).repr_tree [vptr' r full_perm] (fun _ -> [vptr' r full_perm]))
  = (|(fun _ -> [vptr' r full_perm]),
       (| [], Perm.id_n 1, (fun (_:nat) -> Perm.id_n 1) |), (fun _ -> Uv.raise_val (Perm.id_n 1))|)

unfold
let cast_unorm (s : list norm_step) (#t : Type) (x : norm s t) : t
  = norm_spec s t; x

unfold
let cast_norm (s : list norm_step) (#t : Type) (x : t) : norm s t
  = norm_spec s t; x

//let _ = fun r ->
//  assert (print_util (tree_req (test r).repr_tree
//                     #[vptr' r full_perm] #(fun _ -> [vptr' r full_perm])
//                     (cast_unorm normal_tree_cond_steps (test_cond r))))
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
