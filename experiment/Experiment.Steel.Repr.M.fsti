module Experiment.Steel.Repr.M

module U    = Learn.Util
module L    = FStar.List.Pure
module Dl   = Learn.DList
module Fl   = Learn.FList
module Ll   = Learn.List
module SE   = Steel.Effect
module SH   = Experiment.Steel.SteelHack
module Mem  = Steel.Memory
module Perm = Learn.Permutation
module FExt = FStar.FunctionalExtensionality

open Steel.Effect
open Steel.Effect.Atomic


irreducible let __repr_M__ : unit = ()


(*** Steel *)

val focus_rmem_feq (p q r : vprop) (h : rmem p)
  : Lemma (requires can_be_split p q /\ can_be_split q r)
          (ensures  can_be_split p r /\ focus_rmem h q r == h r)

val focus_rmem_trans (p q r : vprop) (h : rmem p)
  : Lemma (requires can_be_split p q /\ can_be_split q r)
          (ensures  can_be_split p r /\ focus_rmem (focus_rmem h q) r == focus_rmem h r)


(* This does not seems provable from the interface of Steel.Effect
// Warning : this can drop some slprops
val change_can_be_split_slprop
      (#opened : Mem.inames)
      (p q : vprop) (_ : squash(can_be_split p q))
  : SteelGhost unit opened p (fun () -> q) (fun _ -> True) (fun h0 () h1 -> h1 q == h0 q)
*)

let subcomp_no_frame_pre
      (#a:Type)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
  : prop
  =
    forall (h0 : rmem pre_g) . (
     (**) equiv_can_be_split pre_g pre_f; (
     req_g h0 ==>
      (req_f (focus_rmem h0 pre_f) /\
      (forall (x : a) (h1 : rmem (post_g x)) . (
        (**) eq_post x; equiv_can_be_split (post_g x) (post_f x); (
        ens_f (focus_rmem h0 pre_f) x (focus_rmem h1 (post_f x)) ==>
        ens_g h0 x h1))))))

val intro_subcomp_no_frame_pre
      (#a:Type)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
      (s_pre :  (h0 : rmem pre_g) -> Lemma
         (requires can_be_split pre_g pre_f /\
                   req_g h0)
         (ensures  req_f (focus_rmem h0 pre_f)))
      (s_post : (h0 : rmem pre_g) -> (x : a) -> (h1 : rmem (post_g x)) -> Lemma
         (requires can_be_split pre_g pre_f /\ can_be_split (post_g x) (post_f x) /\
                   req_g h0 /\ req_f (focus_rmem h0 pre_f) /\
                   ens_f (focus_rmem h0 pre_f) x (focus_rmem h1 (post_f x)))
         (ensures  ens_g h0 x h1))
  : squash (subcomp_no_frame_pre req_f ens_f req_g ens_g eq_pre eq_post)

inline_for_extraction noextract
val unit_steel_subcomp_no_frame
      (#a : Type)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
      (sb_pre : squash (subcomp_no_frame_pre req_f ens_f req_g ens_g eq_pre eq_post))
      ($f : SH.unit_steel a pre_f post_f req_f ens_f)
  : SH.unit_steel a pre_g post_g req_g ens_g

inline_for_extraction noextract
val unit_steel_ghost_subcomp_no_frame
      (#a : Type) (#opened : Mem.inames)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
      (sb_pre : squash (subcomp_no_frame_pre req_f ens_f req_g ens_g eq_pre eq_post))
      ($f : SH.unit_steel_ghost a opened pre_f post_f req_f ens_f)
  : SH.unit_steel_ghost a opened pre_g post_g req_g ens_g


(*** [vprop_list] *)

type vprop_list = list vprop'

[@@ __reduce__]
let rec vprop_of_list' (vpl : vprop_list) : vprop =
  match vpl with
  | [] -> emp
  | v :: vs -> VStar (VUnit v) (vprop_of_list' vs)

let vprop_of_list = vprop_of_list'

val vprop_of_list_can_be_split (vs : vprop_list) (i : nat {i < L.length vs})
  : Lemma (can_be_split (vprop_of_list vs) (VUnit (L.index vs i)))

val vprop_of_list_append (vs0 vs1 : vprop_list)
  : Lemma (equiv (vprop_of_list L.(vs0@vs1)) (vprop_of_list vs0 `star` vprop_of_list vs1))


noeq
type vprop_with_emp : vprop -> Type =
  | VeEmp  : vprop_with_emp emp
  | VeUnit : (v : vprop') -> vprop_with_emp (VUnit v)
  | VeStar : (#vl : vprop) -> (vel : vprop_with_emp vl) ->
             (#vr : vprop) -> (ver : vprop_with_emp vr) ->
             vprop_with_emp (VStar vl vr)
             
let rec flatten_vprop_aux (#vp : vprop) (ve : vprop_with_emp vp) (acc : vprop_list) : GTot vprop_list =
  match ve with
  | VeEmp -> acc
  | VeUnit vp' -> vp' :: acc
  | VeStar vp0 vp1 -> flatten_vprop_aux vp0 (flatten_vprop_aux vp1 acc)

let flatten_vprop (#vp : vprop) (ve : vprop_with_emp vp) : GTot vprop_list = flatten_vprop_aux ve []

val flatten_vprop_aux_eq (#vp : vprop) (ve : vprop_with_emp vp) (acc : vprop_list)
  : Lemma (flatten_vprop_aux ve acc == L.(flatten_vprop ve @ acc))

val flatten_vprop_VStar (#vp0 : vprop) (ve0 : vprop_with_emp vp0) (#vp1 : vprop) (ve1 : vprop_with_emp vp1)
  : Lemma (flatten_vprop (VeStar ve0 ve1) == L.(flatten_vprop ve0 @ flatten_vprop ve1))

val vprop_equiv_flat (vp : vprop) (ve : vprop_with_emp vp)
  : Lemma (equiv (vprop_of_list (flatten_vprop ve)) vp)


(* ALT? dependent arrrow Fin.fin n -> _ *)

let vprop_list_sels_t : vprop_list -> Dl.ty_list =
  L.map Mkvprop'?.t

unfold
let sl_t (vs : vprop_list) : Type = Fl.flist_g (vprop_list_sels_t vs)

unfold
let sl_f (vs : vprop_list) : Type = Fl.flist (vprop_list_sels_t vs)

unfold
let sl_list (vs : vprop_list) : Type = Dl.dlist (vprop_list_sels_t vs)

let vprop_list_sels_t_eq (vs : vprop_list) (i : nat {i < L.length vs})
  : Lemma (ensures L.index (vprop_list_sels_t vs) i == (L.index vs i).t)
          [SMTPat (L.index (vprop_list_sels_t vs) i)]
  = Ll.map_index Mkvprop'?.t vs i

let rec vpl_sels (vs : vprop_list) (sl : t_of (vprop_of_list vs))
  : Tot (sl_list vs) (decreases vs)
  = match (|vs, sl|) <: (vs : vprop_list & t_of (vprop_of_list vs)) with
  | (|[], _|) -> Dl.DNil
  | (|v0 :: vs, (x0, xs)|) -> Dl.DCons v0.t x0 _ (vpl_sels vs xs)

unfold
let vpl_sels_f (vs : vprop_list) (sl : t_of (vprop_of_list vs)) : sl_f vs
  = Fl.flist_of_d (vpl_sels vs sl)

unfold
let sel_list' (#p : vprop) (vs : vprop_list)
      (h : rmem p{can_be_split p (vprop_of_list vs)})
  : GTot (sl_list vs)
  = vpl_sels vs (h (vprop_of_list vs))

unfold
let sel_list (#p : vprop) (vs : vprop_list)
      (h : rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (vprop_of_list vs) /\ True)})
  : GTot (sl_list vs)
  = sel_list' vs h

unfold
let sel_f (#p : vprop) (vs : vprop_list)
      (h : rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (vprop_of_list vs) /\ True)})
  : GTot (sl_f vs)
  = Fl.flist_of_d (sel_list vs h)

unfold
let sel (vs : vprop_list) (h : rmem (vprop_of_list vs))
  : GTot (sl_f vs)
  = sel_f vs h


/// Variant to be used when interacting with Steel
let sel' (vs : vprop_list) (h : rmem (vprop_of_list' vs))
  : sl_t vs
  = Fl.mk_flist_g (vprop_list_sels_t vs) (fun i ->
    (**) vprop_of_list_can_be_split vs i;
    h (VUnit (L.index vs i)))

let sel_f' (vs : vprop_list) (h : rmem (vprop_of_list' vs))
  : GTot (sl_f vs)
  = Fl.flist_of_g (sel' vs h)

val sel_list_eq' (vs : vprop_list) (h : rmem (vprop_of_list vs))
  : Lemma (sel_list vs h == Fl.dlist_of_f_g (sel' vs h))

let sel_f_eq' (vs : vprop_list) (h : rmem (vprop_of_list vs))
  : Lemma (sel_f vs h == sel_f' vs h)
  = sel_list_eq' vs h

val sel_eq' : squash (sel_f' == sel)


unfold
let split_vars (vs0 vs1 : vprop_list) (xs : sl_f (vs0 @ vs1))
  : sl_f vs0 & sl_f vs1
  =
    (**) Ll.map_append Mkvprop'?.t vs0 vs1;
    Fl.splitAt_ty (vprop_list_sels_t vs0) (vprop_list_sels_t vs1) xs

unfold
let split_vars_list (vs0 vs1 : vprop_list) (xs : sl_list (vs0 @ vs1))
  : sl_list vs0 & sl_list vs1
  =
    (**) Ll.map_append Mkvprop'?.t vs0 vs1;
    Dl.splitAt_ty (vprop_list_sels_t vs0) (vprop_list_sels_t vs1) xs

let split_vars__cons (v0 : vprop') (vs0 vs1 : vprop_list) (x0 : v0.t) (xs : sl_list L.(vs0@vs1))
  : Lemma (ensures split_vars_list (v0 :: vs0) vs1 (Dl.DCons v0.t x0 (vprop_list_sels_t L.(vs0@vs1)) xs)
               == (let xs0, xs1 = split_vars_list vs0 vs1 xs in
                   Dl.DCons v0.t x0 (vprop_list_sels_t vs0) xs0, xs1))
  = Ll.map_append Mkvprop'?.t vs0 vs1


val steel_elim_vprop_of_list_append_f (#opened : Mem.inames) (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list L.(vs0@vs1)) (fun () -> vprop_of_list vs0 `star` vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> split_vars vs0 vs1 (sel_f (vs0@vs1) h0)
                        == (sel_f vs0 h1, sel_f vs1 h1))

val steel_intro_vprop_of_list_append_f (#opened : Mem.inames) (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list vs0 `star` vprop_of_list vs1) (fun () -> vprop_of_list L.(vs0@vs1))
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> split_vars vs0 vs1 (sel_f (vs0@vs1) h1)
                        == (sel_f vs0 h0, sel_f vs1 h0))


(***** [vequiv] *)

let vequiv : vprop_list -> vprop_list -> Type = Perm.pequiv #vprop'

unfold
let vequiv_sl (#vs0 #vs1 : vprop_list) (f : vequiv vs0 vs1)
  : Perm.pequiv (vprop_list_sels_t vs0) (vprop_list_sels_t vs1)
  = Perm.map_apply_r f Mkvprop'?.t vs0;
    U.cast #(Perm.perm_f (L.length vs0)) (Perm.perm_f (L.length (vprop_list_sels_t vs0))) f    

unfold
let extract_vars (#src #dst : vprop_list)
                 (p : vequiv src dst)
                 (xs : sl_f src)
  : sl_f dst
  =
    Fl.apply_pequiv (vequiv_sl p) xs

unfold
let extract_vars_f (src dst frame : vprop_list)
                   (p : vequiv src L.(dst@frame))
                   (xs : sl_f src)
  : sl_f dst & sl_f frame
  =
    split_vars dst frame (extract_vars p xs)

let extract_vars_sym_l (#vs0 #vs1 : vprop_list) (f : vequiv vs0 vs1) (xs : sl_f vs0)
  : Lemma (extract_vars (Perm.pequiv_sym f) (extract_vars f xs) == xs)
  =
    Fl.apply_pequiv_sym_l (vequiv_sl f) xs

/// applying a permutation on the context's vprop

val steel_change_vequiv (#vs0 #vs1 : vprop_list) (#opened:Mem.inames) (f : vequiv vs0 vs1)
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel_f vs1 h1 == extract_vars f (sel_f vs0 h0))


(*** [repr_steel_t] *)

type pre_t = vprop_list
type post_t (a : Type) = a -> vprop_list

type req_t (pre : pre_t) = sl_f pre -> Type0
type ens_t (pre : pre_t) (a : Type) (post : post_t a) = sl_f pre -> (x : a) -> sl_f (post x) -> Type0

type repr_steel_t (ek : SH.effect_kind) (a : Type)
       (pre : pre_t) (post : post_t a)
       (req : req_t pre) (ens : ens_t pre a post)
  = SH.steel a
      (vprop_of_list pre) (fun x -> vprop_of_list (post x))
      (requires fun h0 -> req (sel pre h0)) (ensures fun h0 x h1 -> ens (sel pre h0) x (sel_f (post x) h1))
      ek

inline_for_extraction noextract
let repr_steel_subcomp
      (#a : Type) (#pre : pre_t) (#post : post_t a)
      (req_f : req_t pre) (ens_f : ens_t pre a post)
      (req_g : req_t pre) (ens_g : ens_t pre a post)
      (pf_req : (sl0 : sl_f pre) ->
                Lemma (requires req_g sl0) (ensures req_f sl0))
      (pf_ens : (sl0 : sl_f pre) -> (x : a) -> (sl1 : sl_f (post x)) ->
                Lemma (requires req_f sl0 /\ req_g sl0 /\ ens_f sl0 x sl1) (ensures ens_g sl0 x sl1))
      (r : repr_steel_t SH.KSteel a pre post req_f ens_f)
  : repr_steel_t SH.KSteel a pre post req_g ens_g
  = SH.steel_f (fun () ->
      (**) let sl0 : Ghost.erased (t_of (vprop_of_list pre)) = gget (vprop_of_list pre) in
      (**) pf_req (vpl_sels_f pre sl0);
      let x = SH.steel_u r () in
      (**) let sl1 : Ghost.erased (t_of (vprop_of_list (post x))) = gget (vprop_of_list (post x)) in
      (**) pf_ens (vpl_sels_f pre sl0) x (vpl_sels_f (post x) sl1);
      Steel.Effect.Atomic.return x)

(*// This fail, seemingly because of the expansion of the memories when checking the post
[@@ handle_smt_goals ]
let tac () = dump "SMT query"
let steel_of_repr
      (#a : Type) (#pre : pre_t) (#post : post_t a) (#req : req_t pre) (#ens : ens_t pre a post)
      (f : unit_steel a pre post req ens)
  : Steel a pre post req ens
  = f ()*)

[@@ Learn.Tactics.Util.__tac_helper__]
noeq
type to_repr_t (a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
= {
  r_pre  : pre_t;
  r_post : post_t a;
  r_req  : req_t r_pre;
  r_ens  : ens_t r_pre a r_post;
  r_pre_eq  : unit -> Lemma (pre `equiv` vprop_of_list r_pre);
  r_post_eq : (x : a) -> Lemma (post x `equiv` vprop_of_list (r_post x));
  r_req_eq  : (h0 : rmem pre) -> Lemma (req h0 ==
                  r_req (sel r_pre (
                          r_pre_eq ();
                          equiv_can_be_split pre (vprop_of_list r_pre);
                          focus_rmem h0 (vprop_of_list r_pre))));
  r_ens_eq  : (h0 : rmem pre) -> (x : a) -> (h1 : rmem (post x)) -> Lemma (ens h0 x h1 ==
                  r_ens (sel r_pre (
                          r_pre_eq ();
                          equiv_can_be_split pre (vprop_of_list r_pre);
                          focus_rmem h0 (vprop_of_list r_pre)))
                        x
                        (sel (r_post x) (
                          r_post_eq x;
                          equiv_can_be_split (post x) (vprop_of_list (r_post x));
                          focus_rmem h1 (vprop_of_list (r_post x)))))
}

inline_for_extraction noextract
val steel_of_repr
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      (f : repr_steel_t SH.KSteel a tr.r_pre tr.r_post tr.r_req tr.r_ens)
  : SH.unit_steel a pre post req ens

inline_for_extraction noextract
val repr_steel_of_steel
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      ($f  : SH.unit_steel a pre post req ens)
  : repr_steel_t SH.KSteel a tr.r_pre tr.r_post tr.r_req tr.r_ens 

inline_for_extraction noextract
val steel_ghost_of_repr
      (#a : Type) (#opened : Mem.inames)
      (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      (f : repr_steel_t (SH.KGhost opened) a tr.r_pre tr.r_post tr.r_req tr.r_ens)
  : SH.unit_steel_ghost a opened pre post req ens

inline_for_extraction noextract
val repr_steel_of_steel_ghost
      (#a : Type) (#opened : Mem.inames)
      (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      ($f  : SH.unit_steel_ghost a opened pre post req ens)
  : repr_steel_t (SH.KGhost opened) a tr.r_pre tr.r_post tr.r_req tr.r_ens


(*** [prog_tree] *)

noeq
type prog_tree : (a : Type u#a) -> Type u#(max (a+1) 2) =
  // A specification of the subprogram, used to represent function calls
  | Tspec  : (a : Type u#a) -> (pre : pre_t) -> (post : post_t a) ->
             (req : req_t pre) -> (ens : ens_t pre a post) ->
             prog_tree a
  // A Steel specification, used to represent calls to Steel functions
  | TspecS : (a : Type u#a) -> (pre : SE.pre_t) -> (post : SE.post_t a) ->
             (req : SE.req_t pre) -> (ens : SE.ens_t pre a post) ->
             prog_tree a
  // return, with a hint for introducing dependencies in the returned value
  | Tret   : (a : Type u#a) -> (x : a) -> (sl_hint : post_t a) ->
             prog_tree a
  // bind
  | Tbind  : (a : Type u#a) -> (b : Type u#a) ->
             (f : prog_tree a) -> (g : a -> prog_tree b) ->
             prog_tree b
  // bind pure, models a polymonadic bind between PURE and our monad
  | TbindP : (a : Type u#a) -> (b : Type u#a) ->
             (wp : pure_wp a) -> (g : a -> prog_tree b) ->
             prog_tree b
  // if-then-else
  | Tif    : (a : Type u#a) -> (guard : bool) ->
             (thn : prog_tree a) -> (els : prog_tree a) ->
             prog_tree a


(*** slprop unification conditions *)

(* TODO:
   - ? equalities vs vequiv
      + Tspec : post x == post' x @ frame, allow shuffle at the end
   - ~pr ! allow assumptions -> VC
   - ALT: recursively defined type *)

[@@ Learn.Tactics.Util.__tac_helper__]
noeq
type tree_cond_Spec (a : Type) (pre : pre_t) (post : post_t a) = {
  tcs_pre     : pre_t;
  tcs_post    : post_t a;
  tcs_frame   : vprop_list;
  tcs_pre_eq  : vequiv tcs_pre L.(pre @ tcs_frame);
  tcs_post_eq : (x : a) -> vequiv L.(post x @ tcs_frame) (tcs_post x)
}

noeq
type tree_cond : (#a : Type u#a) -> (t : prog_tree a) -> (pre : pre_t) -> (post : post_t a) -> Type u#(max (a+1) 2) =
  | TCspec  : (#a : Type u#a) -> (#pre : pre_t) -> (#post : post_t a) ->
              (#req : req_t pre) -> (#ens : ens_t pre a post) ->
              (tcs : tree_cond_Spec a pre post) ->
              tree_cond (Tspec a pre post req ens) tcs.tcs_pre tcs.tcs_post
  | TCspecS : (#a : Type u#a) -> (#pre : SE.pre_t) -> (#post : SE.post_t a) ->
              (#req : SE.req_t pre) -> (#ens : SE.ens_t pre a post) ->
              (tr  : to_repr_t a pre post req ens) ->
              (tcs : tree_cond_Spec a tr.r_pre tr.r_post) ->
              tree_cond (TspecS a pre post req ens) tcs.tcs_pre tcs.tcs_post
  | TCret   : (#a : Type u#a) -> (#x : a) -> (#sl_hint : post_t a) ->
              (pre : pre_t) -> (post : post_t a) ->
              (p : vequiv pre (post x)) ->
              tree_cond (Tret a x sl_hint) pre post
  | TCbind  : (#a : Type u#a) -> (#b : Type u#a) -> (#f : prog_tree a) -> (#g : (a -> prog_tree b)) ->
              (pre : pre_t) -> (itm : post_t a) -> (post : post_t b) ->
              (cf : tree_cond f pre itm) -> (cg : ((x : a) -> tree_cond (g x) (itm x) post)) ->
              tree_cond (Tbind a b f g) pre post
  | TCbindP : (#a : Type u#a) -> (#b : Type u#a) ->
              (#wp : pure_wp a) -> (#g : (a -> prog_tree b)) ->
              (pre : pre_t) -> (post : post_t b) ->
              (cg : ((x : a) -> tree_cond (g x) pre post)) ->
              tree_cond (TbindP a b wp g) pre post
  | TCif    : (#a : Type u#a) -> (#guard : bool) -> (#thn : prog_tree a) -> (#els : prog_tree a) ->
              (pre : pre_t) -> (post : post_t a) ->
              (cthn : tree_cond thn pre post) -> (cels : tree_cond els pre post) ->
              tree_cond (Tif a guard thn els) pre post

(**** Shape *)

type shape_tree : (pre_n : nat) -> (post_n : nat) -> Type =
  | Sspec  : (pre_n : nat) -> (post_n : nat) -> (frame_n : nat) ->
             (p0 : Perm.perm_f_list (pre_n  + frame_n)) ->
             (p1 : Perm.perm_f_list (post_n + frame_n)) ->
             shape_tree (pre_n + frame_n) (post_n + frame_n)
  | Sret   : (n : nat) -> (p : Perm.perm_f_list n) ->
             shape_tree n n
  | Sbind  : (pre_n : nat) -> (itm_n : nat) -> (post_n : nat) ->
             (f : shape_tree pre_n itm_n) -> (g : shape_tree itm_n post_n) ->
             shape_tree pre_n post_n
  | SbindP : (pre_n : nat) -> (post_n : nat) ->
             (g : shape_tree pre_n post_n) ->
             shape_tree pre_n post_n
  | Sif    : (pre_n : nat) -> (post_n : nat) ->
             (thn : shape_tree pre_n post_n) -> (els : shape_tree pre_n post_n) ->
             shape_tree pre_n post_n

unfold
let tree_cond_has_shape_Spec
      (a : Type) (pre : pre_t) (post : post_t a) (tcs : tree_cond_Spec a pre post)
      (#post_n : nat) (s : shape_tree (L.length tcs.tcs_pre) post_n)
  : prop
  = match s with
  | Sspec pre_n post_n frame_n p0' p1' ->
    pre_n = L.length pre /\
    frame_n = L.length tcs.tcs_frame /\
    Ll.list_eq
      (Perm.perm_f_to_list
        (U.cast #(Perm.perm_f L.(length tcs.tcs_pre)) (Perm.perm_f (pre_n + frame_n))
          tcs.tcs_pre_eq))
      p0' /\
   (forall (x : a) .
     L.length (post  x) = post_n /\
     L.length (tcs.tcs_post x) = post_n + frame_n /\ (* already implied ? *)
     Ll.list_eq
       (Perm.perm_f_to_list
         (U.cast #(Perm.perm_f L.(length (post x @ tcs.tcs_frame)))
                  (Perm.perm_f (post_n + frame_n))
                  (tcs.tcs_post_eq x)))
       p1')
  | _ -> False

[@@ strict_on_arguments [4;6]] (* strict on c;s *)
let rec tree_cond_has_shape
      (#a : Type) (#pre : pre_t) (#post0 : post_t a) (#t : prog_tree a)
      (c : tree_cond t pre post0)
      (#post_n : nat) (s : shape_tree (L.length pre) post_n)
  : Pure prop (requires True) (ensures fun p -> p ==> (forall (x : a) . L.length (post0 x) = post_n)) (decreases c)
  = match c with
  | TCspec #a #pre #post tcs -> tree_cond_has_shape_Spec a pre post tcs s
  | TCspecS #a tr tcs -> tree_cond_has_shape_Spec a tr.r_pre tr.r_post tcs s
  | TCret #a pre post p ->
      (match s with
      | Sret n p' ->
        Ll.list_eq (Perm.perm_f_to_list #n p) p' /\
       (forall (x : a) . L.length (post x) = n)
      | _ -> False)
  | TCbind #a #b pre itm post f g ->
      (match s with
      | Sbind _ itm_n post_n s_f s_g ->
        tree_cond_has_shape f s_f /\
       (forall (x : a) . tree_cond_has_shape (g x) s_g) /\
       (forall (y : b) . L.length (post y) = post_n)
      | _ -> False)
  | TCbindP #a #b pre post g ->
      (match s with
      | SbindP _ post_n s_g ->
        (forall (x : a) . tree_cond_has_shape (g x) s_g) /\
        (forall (y : b) . L.length (post y) = post_n)
      | _ -> False)
  | TCif #a pre post thn els ->
      (match s with
      | Sif _ _ s_thn s_els ->
        tree_cond_has_shape thn s_thn /\
        tree_cond_has_shape els s_els
      | _ -> False)

noeq inline_for_extraction noextract
type prog_cond (#a : Type) (t : prog_tree a) (pre : pre_t) (post : post_t a) = {
  pc_tree     : tree_cond t pre post;
  pc_post_len : nat;
  pc_shape    : (s : shape_tree (L.length pre) pc_post_len {tree_cond_has_shape pc_tree s})
}


(**** requires / ensures *)

(** spec *)

let spec_req (#a : Type) (#pre : pre_t) (#post : post_t a) (tcs : tree_cond_Spec a pre post)
             (req : req_t pre)
  : req_t tcs.tcs_pre
  = fun sl0 ->
      req (extract_vars_f tcs.tcs_pre pre tcs.tcs_frame tcs.tcs_pre_eq sl0)._1

let spec_ens (#a : Type) (#pre : pre_t) (#post : post_t a) (tcs : tree_cond_Spec a pre post)
             (ens : ens_t pre a post)
  : ens_t tcs.tcs_pre a tcs.tcs_post
  = fun sl0' x sl1' ->
      let sl0, frame0 = extract_vars_f tcs.tcs_pre pre tcs.tcs_frame tcs.tcs_pre_eq sl0' in
      let sl1, frame1 = extract_vars_f (tcs.tcs_post x) (post x) tcs.tcs_frame
                                       (Perm.pequiv_sym (tcs.tcs_post_eq x)) sl1' in
      frame1 == frame0 /\ ens sl0 x sl1

(** return *)

let return_req (pre : pre_t) : req_t pre
  = fun _ -> True

let return_ens (#a : Type) (x : a) (p : post_t a) : ens_t (p x) a p
  = fun sl0 r sl1 ->
      r == x /\ sl1 == sl0

(** bind *)

let bind_req (#a : Type)
      (#pre : pre_t) (#itm : post_t a)
      (req_f : req_t pre) (ens_f : ens_t pre a itm)
      (req_g : (x:a) -> req_t (itm x))
  : req_t pre
  = fun sl0 -> req_f sl0 /\
      (forall (x : a) (sl1 : sl_f (itm x)) .
        ens_f sl0 x sl1 ==> req_g x sl1)

/// Unlike the bind combiner of Steel, our ensures clause does not recall the pre-condition of [f] for
/// the reason explained on [Experiment.Repr.Fun.tree_ens]

let bind_ens (#a : Type) (#b : Type)
      (#pre : pre_t) (#itm : post_t a) (#post : post_t b)
      (ens_f : ens_t pre a itm) (ens_g : (x:a) -> ens_t (itm x) b post)
  : ens_t pre b post
  = fun sl0 y sl2 ->
      (exists (x : a) (sl1 : sl_f (itm x)) .
        ens_f sl0 x sl1 /\
        ens_g x sl1 y sl2)

(** bind_pure *)

let bind_pure_req (#a : Type) (wp : pure_wp a)
      (#pre : pre_t)
      (req : a -> req_t pre)
  : req_t pre
  = fun sl0 -> wp (fun x -> req x sl0)

let bind_pure_ens (#a : Type) (#b : Type)
      (wp : pure_wp a)
      (#pre : pre_t) (#post : post_t b)
      (ens : a -> ens_t pre b post)
  : ens_t pre b post
  = fun sl0 y sl1 -> (exists (x:a) . as_ensures wp x /\ ens x sl0 y sl1)

(** if-then-else *)

let ite_req (#a : Type) (guard : bool) (#pre : pre_t)
      (req_thn : req_t pre) (req_els : req_t pre)
  : req_t pre
  = fun sl0 -> if guard then req_thn sl0 else req_els sl0

let ite_ens (#a : Type) (guard : bool) (#pre : pre_t) (#post : post_t a)
      (ens_thn : ens_t pre a post) (ens_els : ens_t pre a post)
  : ens_t pre a post
  = fun sl0 x sl1 -> if guard then ens_thn sl0 x sl1 else ens_els sl0 x sl1


(** prog_tree *)

[@@ strict_on_arguments [4]] (* strict on c *)
let rec tree_req (#a : Type u#a) (t : prog_tree a)
                 (#pre : pre_t) (#post : post_t a) (c : tree_cond t pre post)
                 (sl0 : sl_f pre)
  : Tot Type0 (decreases t) =
  match c with
  | TCspec #_ #pre #_ #req #_  tcs ->
             spec_req tcs req sl0
  | TCspecS #_ tr tcs ->
             spec_req tcs tr.r_req sl0
  | TCret #_ #_  pre _  _ ->
             return_req pre sl0
  | TCbind #_ #_ #f #g  pre itm _  cf cg ->
             bind_req (tree_req f cf) (tree_ens f cf) (fun x -> tree_req (g x) (cg x)) sl0
  | TCbindP #_ #_ #wp #g  pre _  cg ->
             bind_pure_req wp (fun x -> tree_req (g x) (cg x)) sl0
  | TCif #a #guard  pre _ thn els ->
             ite_req #a guard (tree_req _ thn) (tree_req _ els) sl0

and tree_ens (#a : Type u#a) (t : prog_tree a)
             (#pre : pre_t) (#post : post_t a) (c : tree_cond t pre post)
             (sl0 : sl_f pre) (res : a) (sl1 : sl_f (post res))
  : Tot Type0 (decreases t) =
  match c with
  | TCspec #a #pre #post #req #ens  tcs ->
             spec_ens tcs ens sl0 res sl1
  | TCspecS #_ tr tcs ->
             spec_ens tcs tr.r_ens sl0 res sl1
  | TCret #a #x  pre post  p ->
                res == x /\
               (let sl0' = extract_vars p sl0 in
                sl1 == sl0')
  | TCbind #_ #_ #f #g  pre itm post  cf cg ->
             bind_ens (tree_ens f cf) (fun x -> tree_ens (g x) (cg x)) sl0 res sl1
  | TCbindP #_ #_ #wp #g  pre post  cg ->
             bind_pure_ens wp (fun x -> tree_ens (g x) (cg x)) sl0 res sl1
  | TCif #a #guard  pre post thn els ->
             ite_ens #a guard (tree_ens _ thn) (tree_ens _ els) sl0 res sl1


(*** "Monad" *)

/// We define a "monad" (which does not satisfy the monad laws) on a [repr] type which contains a representation
/// of the program as a tree and a corresponding steel function.

noeq inline_for_extraction noextract
type repr (ek : SH.effect_kind) (a : Type) = {
  repr_tree  : prog_tree a;
  repr_steel : (pre : pre_t) -> (post : post_t a) -> (c : tree_cond repr_tree pre post) ->
               repr_steel_t ek a pre post (tree_req repr_tree c) (tree_ens repr_tree c)
}


inline_for_extraction noextract
let repr_of_steel_steel
      (a : Type) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
      (tcs : tree_cond_Spec a pre post)
      ($f : repr_steel_t SH.KSteel a pre post req ens)
  : (let c = TCspec #a #pre #post #req #ens tcs in
     repr_steel_t SH.KSteel a tcs.tcs_pre tcs.tcs_post (tree_req _ c) (tree_ens _ c))
  = SH.steel_f (fun () ->
    (**) steel_change_vequiv tcs.tcs_pre_eq;
    (**) steel_elim_vprop_of_list_append_f pre tcs.tcs_frame;
    let x = SH.steel_u f () in
    (**) steel_intro_vprop_of_list_append_f (post x) tcs.tcs_frame;
    (**) let sl1' = gget (vprop_of_list L.(post x @ tcs.tcs_frame)) in
    (**) steel_change_vequiv (tcs.tcs_post_eq x);
    (**) let sl1'' = gget (vprop_of_list (tcs.tcs_post x)) in
    (**) assert (vpl_sels_f (tcs.tcs_post x) sl1''
    (**)      == extract_vars (tcs.tcs_post_eq x) (vpl_sels_f L.(post x @ tcs.tcs_frame) sl1'));
    (**) extract_vars_sym_l (tcs.tcs_post_eq x) (vpl_sels_f L.(post x @ tcs.tcs_frame) sl1');
    Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let repr_of_steel_ghost_steel
      (a : Type) (opened : Mem.inames) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
      (tcs : tree_cond_Spec a pre post)
      ($f : repr_steel_t (SH.KGhost opened) a pre post req ens)
  : (let c = TCspec #a #pre #post #req #ens tcs in
     repr_steel_t (SH.KGhost opened) a tcs.tcs_pre tcs.tcs_post (tree_req _ c) (tree_ens _ c))
  = SH.ghost_f #opened (fun () ->
    (**) steel_change_vequiv tcs.tcs_pre_eq;
    (**) steel_elim_vprop_of_list_append_f pre tcs.tcs_frame;
    let x = SH.ghost_u f () in
    (**) steel_intro_vprop_of_list_append_f (post x) tcs.tcs_frame;
    (**) let sl1' = gget (vprop_of_list L.(post x @ tcs.tcs_frame)) in
    (**) steel_change_vequiv (tcs.tcs_post_eq x);
    (**) let sl1'' = gget (vprop_of_list (tcs.tcs_post x)) in
    (**) assert (vpl_sels_f (tcs.tcs_post x) sl1''
    (**)      == extract_vars (tcs.tcs_post_eq x) (vpl_sels_f L.(post x @ tcs.tcs_frame) sl1'));
    (**) extract_vars_sym_l (tcs.tcs_post_eq x) (vpl_sels_f L.(post x @ tcs.tcs_frame) sl1');
    (**) noop ();
    x)


[@@ __repr_M__]
let tree_of_steel_r
      (#ek : SH.effect_kind) (#a : Type)
      (#pre : pre_t) (#post : post_t a) (#req : req_t pre) (#ens : ens_t pre a post)
      ($f : repr_steel_t ek a pre post req ens)
  : prog_tree a
  = Tspec a pre post req ens

[@@ __repr_M__]
inline_for_extraction noextract
let repr_of_steel_r
      (#a : Type) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
      ($f : repr_steel_t SH.KSteel a pre post req ens)
  : repr SH.KSteel a
  = {
    repr_tree  = tree_of_steel_r f;
    repr_steel = (fun pre'0 post'0 c ->
                    let TCspec tcs = c in
                    repr_of_steel_steel a pre post req ens tcs f)
  }

[@@ __repr_M__]
inline_for_extraction noextract
let repr_of_steel_ghost_r
      (#a : Type) (#opened : Mem.inames) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
      ($f : repr_steel_t (SH.KGhost opened) a pre post req ens)
  : repr (SH.KGhost opened) a
  = {
    repr_tree  = tree_of_steel_r f;
    repr_steel = (fun pre'0 post'0 c ->
                    let TCspec tcs = c in
                    repr_of_steel_ghost_steel a opened pre post req ens tcs f)
  }


[@@ __repr_M__]
let tree_of_steel
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      ($f : SH.unit_steel a pre post req ens)
  : prog_tree a
  = TspecS a pre post req ens

[@@ __repr_M__]
inline_for_extraction noextract
let repr_of_steel
      (#a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      ($f : SH.unit_steel a pre post req ens)
  : repr SH.KSteel a
  = {
    repr_tree  = tree_of_steel f;
    repr_steel = (fun pre'0 post'0 c ->
                    let TCspecS tr tcs = c in
                    repr_of_steel_steel a tr.r_pre tr.r_post tr.r_req tr.r_ens
                                        tcs (repr_steel_of_steel tr f))
  }

[@@ __repr_M__]
inline_for_extraction noextract
let repr_of_steel_ghost
      (#a : Type) (#opened : Mem.inames)
      (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      ($f : SH.unit_steel_ghost a opened pre post req ens)
  : repr (SH.KGhost opened) a
  = {
    repr_tree  = TspecS a pre post req ens;
    repr_steel = (fun pre'0 post'0 c ->
                    let TCspecS tr tcs = c in
                    repr_of_steel_ghost_steel a opened tr.r_pre tr.r_post tr.r_req tr.r_ens
                                        tcs (repr_steel_of_steel_ghost tr f))
  }



inline_for_extraction noextract
let return_steel
      (a : Type) (x : a) (sl_hint : post_t a)
      (pre : pre_t) (post : post_t a)
      (p : vequiv pre (post x))
  : (let c = TCret #a #x #sl_hint pre post p in
     repr_steel_t SH.KSteel a pre post (tree_req _ c) (tree_ens _ c))
  = SH.steel_f (fun () ->
    (**) steel_change_vequiv p;
    Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let return_ghost_steel
      (a : Type) (opened : Mem.inames) (x : a) (sl_hint : post_t a)
      (pre : pre_t) (post : post_t a)
      (p : vequiv pre (post x))
  : (let c = TCret #a #x #sl_hint pre post p in
     repr_steel_t (SH.KGhost opened) a pre post (tree_req _ c) (tree_ens _ c))
  = SH.ghost_f #opened (fun () ->
    (**) steel_change_vequiv p;
    x)

[@@ __repr_M__]
inline_for_extraction noextract
let return_hint (#a : Type) (x : a) (sl_hint : post_t a)
  : repr SH.KSteel a
  = {
    repr_tree  = Tret a x sl_hint;
    repr_steel = (fun pre0 post0 c ->
        let TCret pre post p = c in
        return_steel a x sl_hint pre post p)
  }

[@@ __repr_M__]
inline_for_extraction noextract
let return (#a : Type) (x : a) : repr SH.KSteel a
  = return_hint x (fun _ -> [])

[@@ __repr_M__]
inline_for_extraction noextract
let return_ghost_hint (#a : Type) (#opened : Mem.inames) (x : a) (sl_hint : post_t a)
  : repr (SH.KGhost opened) a
  = {
    repr_tree  = Tret a x sl_hint;
    repr_steel = (fun pre0 post0 c ->
        let TCret pre post p = c in
        return_ghost_steel a opened x sl_hint pre post p)
  }

[@@ __repr_M__]
inline_for_extraction noextract
let return_ghost (#a : Type) (#opened : Mem.inames) (x : a) : repr (SH.KGhost opened) a
  = return_ghost_hint x (fun _ -> [])



val elim_tree_req_bind (#a #b : Type) (f : prog_tree a) (g : a -> prog_tree b)
      (#pre : pre_t) (#post : post_t b) (#itm : post_t a)
      (cf  : tree_cond f pre itm) (cg : (x:a) -> tree_cond (g x) (itm x) post)
      (sl0 : t_of (vprop_of_list pre))
  : Lemma (requires tree_req _ (TCbind #a #b #f #g pre itm post cf cg) (vpl_sels_f pre sl0))
          (ensures  tree_req f cf (vpl_sels_f pre sl0) /\
                    (forall (x : a) (sl1 : t_of (vprop_of_list (itm x))) .
                      tree_ens f cf (vpl_sels_f pre sl0) x (vpl_sels_f (itm x) sl1) ==>
                      tree_req (g x) (cg x) (vpl_sels_f (itm x) sl1)))

val intro_tree_ens_bind (#a #b : Type) (f : prog_tree a) (g : a -> prog_tree b)
      (#pre : pre_t) (#post : post_t b) (#itm : post_t a)
      (cf  : tree_cond f pre itm) (cg : (x:a) -> tree_cond (g x) (itm x) post)
      (sl0 : t_of (vprop_of_list pre)) (x : a) (sl1 : t_of (vprop_of_list (itm x)))
      (y : b) (sl2 : t_of (vprop_of_list (post y)))
  : Lemma (requires tree_req f cf (vpl_sels_f pre sl0) /\
                    tree_ens f cf (vpl_sels_f pre sl0) x (vpl_sels_f (itm x) sl1) /\
                    tree_ens (g x) (cg x) (vpl_sels_f (itm x) sl1) y (vpl_sels_f (post y) sl2))
          (ensures  tree_ens _ (TCbind #a #b #f #g pre itm post cf cg)
                             (vpl_sels_f pre sl0) y (vpl_sels_f (post y) sl2))

inline_for_extraction noextract
let bind_steel
      (a : Type) (b : Type) (f : prog_tree a) (g : (a -> prog_tree b))
      (pre : pre_t) (itm : post_t a) (post : post_t b)
      (cf : tree_cond f pre itm) (cg : ((x : a) -> tree_cond (g x) (itm x) post))
      ($rf : repr_steel_t SH.KSteel a pre itm (tree_req f cf) (tree_ens f cf))
      ($rg : (x : a) -> repr_steel_t SH.KSteel b (itm x) post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbind #a #b #f #g pre itm post cf cg in
     repr_steel_t SH.KSteel b pre post (tree_req _ c) (tree_ens _ c))
  = SH.steel_f (fun () ->
    (**) let sl0 = gget (vprop_of_list pre) in
    (**) elim_tree_req_bind f g cf cg sl0;
    let x = SH.steel_u rf () in
    (**) let sl1 = gget (vprop_of_list (itm x)) in
    let y = SH.steel_u (rg x) () in
    (**) let sl2 = gget (vprop_of_list (post y)) in
    (**) intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2;
    Steel.Effect.Atomic.return y)

inline_for_extraction noextract
let bind_ghost_steel
      (a : Type) (b : Type) (opened : Mem.inames) (f : prog_tree a) (g : (a -> prog_tree b))
      (pre : pre_t) (itm : post_t a) (post : post_t b)
      (cf : tree_cond f pre itm) (cg : ((x : a) -> tree_cond (g x) (itm x) post))
      ($rf : repr_steel_t (SH.KGhost opened) a pre itm (tree_req f cf) (tree_ens f cf))
      ($rg : (x : a) -> repr_steel_t (SH.KGhost opened) b (itm x) post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbind #a #b #f #g pre itm post cf cg in
     repr_steel_t (SH.KGhost opened) b pre post (tree_req _ c) (tree_ens _ c))
  = SH.ghost_f #opened (fun () ->
    (**) let sl0 = gget (vprop_of_list pre) in
    (**) elim_tree_req_bind f g cf cg sl0;
    let x = SH.ghost_u rf () in
    (**) let sl1 = gget (vprop_of_list (itm x)) in
    let y = SH.ghost_u (rg x) () in
    (**) let sl2 = gget (vprop_of_list (post y)) in
    (**) intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2;
    (**) noop ();
    y)

[@@ __repr_M__]
inline_for_extraction noextract
let bind (#a #b : Type) (f : repr SH.KSteel a) (g : a -> repr SH.KSteel b)
  : repr SH.KSteel b
  = {
    repr_tree  = Tbind a b f.repr_tree (fun x -> (g x).repr_tree);
    repr_steel = (fun pre0 post0 c ->
                    let (TCbind #a' #b' #tf #tg pre itm post cf cg) = c in
                    let rg (x : a) : repr_steel_t SH.KSteel b (itm x) post _ _
                                   = (g x).repr_steel _ _ (cg x) in
                    bind_steel a b tf tg pre itm post cf cg (f.repr_steel _ _ cf) rg)
  }

[@@ __repr_M__]
inline_for_extraction noextract
let bind_ghost (#a #b : Type) (#opened : Mem.inames)
               (f : repr (SH.KGhost opened) a) (g : a -> repr (SH.KGhost opened) b)
  : repr (SH.KGhost opened) b
  = {
    repr_tree  = Tbind a b f.repr_tree (fun x -> (g x).repr_tree);
    repr_steel = (fun pre0 post0 c ->
                    let (TCbind #a' #b' #tf #tg pre itm post cf cg) = c in
                    let rg (x : a) : repr_steel_t (SH.KGhost opened) b (itm x) post _ _
                                   = (g x).repr_steel _ _ (cg x) in
                    bind_ghost_steel a b opened tf tg pre itm post cf cg (f.repr_steel _ _ cf) rg)
  }


inline_for_extraction noextract
let bindP_steel
      (a : Type) (b : Type) (wp : pure_wp a) ($f : unit -> PURE a wp) (g : (a -> prog_tree b))
      (pre : pre_t) (post : post_t b)
      (cg : ((x : a) -> tree_cond (g x) pre post))
      ($rg : (x : a) -> repr_steel_t SH.KSteel b pre post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbindP #a #b #wp #g pre post cg in
     repr_steel_t SH.KSteel b pre post (tree_req _ c) (tree_ens _ c))
  = 
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    SH.steel_f (fun () ->
    let x = f () in
    SH.steel_u (rg x) ())

inline_for_extraction noextract
let bindP_ghost_steel
      (a : Type) (b : Type) (opened : Mem.inames) (wp : pure_wp a) ($f : unit -> GHOST a wp) (g : (a -> prog_tree b))
      (pre : pre_t) (post : post_t b)
      (cg : ((x : a) -> tree_cond (g x) pre post))
      ($rg : (x : a) -> repr_steel_t (SH.KGhost opened) b pre post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbindP #a #b #wp #g pre post cg in
     repr_steel_t (SH.KGhost opened) b pre post (tree_req _ c) (tree_ens _ c))
  =
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    SH.ghost_f #opened (fun () ->
    let x = f () in
    SH.ghost_u (rg x) ())

[@@ __repr_M__]
inline_for_extraction noextract
let bindP (#a #b : Type) (wp : pure_wp a) ($f : unit -> PURE a wp) (g : a -> repr SH.KSteel b)
  : repr SH.KSteel b
  = {
    repr_tree  = TbindP a b wp (fun x -> (g x).repr_tree);
    repr_steel = (fun pre0 post0 c ->
                    let (TCbindP #a' #b' #wp #tg pre post cg) = c in
                    let rg (x : a) : repr_steel_t SH.KSteel b pre post _ _
                                   = (g x).repr_steel _ _ (cg x) in
                    bindP_steel a b wp f tg pre post cg rg)
  }

[@@ __repr_M__]
inline_for_extraction noextract
let bindP_ghost (#a #b : Type) (#opened : Mem.inames)
                (wp : pure_wp a) ($f : unit -> GHOST a wp) (g : a -> repr (SH.KGhost opened) b)
  : repr (SH.KGhost opened) b
  = {
    repr_tree  = TbindP a b wp (fun x -> (g x).repr_tree);
    repr_steel = (fun pre0 post0 c ->
                    let (TCbindP #a' #b' #wp #tg pre post cg) = c in
                    let rg (x : a) : repr_steel_t (SH.KGhost opened) b pre post _ _
                                   = (g x).repr_steel _ _ (cg x) in
                    bindP_ghost_steel a b opened wp f tg pre post cg rg)
  }


inline_for_extraction noextract
let ite_steel
      (a : Type) (guard : bool) (thn : prog_tree a) (els : prog_tree a)
      (pre : pre_t) (post : post_t a)
      (cthn : tree_cond thn pre post) (cels : tree_cond els pre post)
      ($rthn : repr_steel_t SH.KSteel a pre post (tree_req thn cthn) (tree_ens thn cthn))
      ($rels : repr_steel_t SH.KSteel a pre post (tree_req els cels) (tree_ens els cels))
  : (let c = TCif #a #guard #thn #els pre post cthn cels in
     repr_steel_t SH.KSteel a pre post (tree_req _ c) (tree_ens _ c))
  = SH.steel_f (fun () ->
    if guard then SH.steel_u rthn () else SH.steel_u rels ())

inline_for_extraction noextract
let ite_ghost_steel
      (a : Type) (opened : Mem.inames) (guard : bool) (thn : prog_tree a) (els : prog_tree a)
      (pre : pre_t) (post : post_t a)
      (cthn : tree_cond thn pre post) (cels : tree_cond els pre post)
      ($rthn : repr_steel_t (SH.KGhost opened) a pre post (tree_req thn cthn) (tree_ens thn cthn))
      ($rels : repr_steel_t (SH.KGhost opened) a pre post (tree_req els cels) (tree_ens els cels))
  : (let c = TCif #a #guard #thn #els pre post cthn cels in
     repr_steel_t (SH.KGhost opened) a pre post (tree_req _ c) (tree_ens _ c))
  = SH.ghost_f #opened (fun () ->
    if guard then SH.ghost_u rthn () else SH.ghost_u rels ())

[@@ __repr_M__]
inline_for_extraction noextract
let ite (#a : Type) (guard : bool) (thn els : repr SH.KSteel a)
  : repr SH.KSteel a
  = {
    repr_tree  = Tif a guard thn.repr_tree els.repr_tree;
    repr_steel = (fun pre0 post0 c ->
                    let (TCif pre post cthn cels) = c in
                    ite_steel a guard _ _ pre post cthn cels
                       (thn.repr_steel _ _ cthn) (els.repr_steel _ _ cels))
  }

[@@ __repr_M__]
inline_for_extraction noextract
let ite_ghost (#a : Type) (#opened : Mem.inames) (guard : bool) (thn els : repr (SH.KGhost opened) a)
  : repr (SH.KGhost opened) a
  = {
    repr_tree  = Tif a guard thn.repr_tree els.repr_tree;
    repr_steel = (fun pre0 post0 c ->
                    let (TCif pre post cthn cels) = c in
                    ite_ghost_steel a opened guard _ _ pre post cthn cels
                       (thn.repr_steel _ _ cthn) (els.repr_steel _ _ cels))
  }


inline_for_extraction noextract
let ghost_to_steel_steel (a : Type) (t : prog_tree (Ghost.erased a)) (pre : pre_t) (post : post_t (Ghost.erased a))
      (c : tree_cond t pre post)
      ($r : repr_steel_t (SH.KGhost Set.empty) (Ghost.erased a) pre post (tree_req t c) (tree_ens t c))
  : repr_steel_t SH.KSteel (Ghost.erased a) pre post (tree_req t c) (tree_ens t c)
  = SH.steel_f (SH.ghost_u r)

[@@ __repr_M__]
inline_for_extraction noextract
let ghost_to_steel (#a : Type) (f : repr (SH.KGhost Set.empty) (Ghost.erased a))
  : repr SH.KSteel (Ghost.erased a)
  = {
    repr_tree  = f.repr_tree;
    repr_steel = (fun pre post c ->
                    ghost_to_steel_steel a f.repr_tree pre post c (f.repr_steel _ _ c))
  }

(*
inline_for_extraction noextract
let ghost_to_steel_steel_ct_aux (a : Type) (t : prog_tree a) (pre : pre_t) (post : post_t a)
      (c : tree_cond t pre post)
      ($r : repr_steel_t (SH.KGhost Set.empty) a pre post (tree_req t c) (tree_ens t c))
  : SteelGhost (Ghost.erased a) Set.empty
             (vprop_of_list pre) (fun x -> vprop_of_list (post (Ghost.reveal x)))
             (fun h0 -> tree_req t c (sel pre h0))
             (fun h0 x h1 -> tree_ens t c (sel pre h0) (Ghost.reveal x) (sel (post (Ghost.reveal x)) h1))
  = let x = ghost_u r () in Ghost.hide x

inline_for_extraction noextract
let ghost_to_steel_steel_ct (a : Type) (t : prog_tree a) (pre : pre_t) (post : post_t a)
      (c : tree_cond t pre post)
      ($r : repr_steel_t (SH.KGhost Set.empty) a pre post (tree_req t c) (tree_ens t c))
      (rv : (x : Ghost.erased a) -> (x' : a { x' == Ghost.reveal x }))
  : repr_steel_t SH.KSteel a pre post (tree_req t c) (tree_ens t c)
  = SH.steel_f (fun () ->
    let x = ghost_to_steel_steel_ct_aux a t pre post c r in
    change_equal_slprop (vprop_of_list (post (Ghost.reveal x))) (vprop_of_list (post (rv x)));
    Steel.Effect.Atomic.return (rv x)
  )
*)

// TODO: SteelAtomic
