module Experiment.Steel.Repr.M

module U    = Learn.Util
module L    = FStar.List.Pure
module Dl   = Learn.DList
module Fl   = Learn.FList
module Ll   = Learn.List
module SE   = Steel.Effect
module SH   = Experiment.Steel.Steel
module Itf  = Experiment.Steel.Interface
module Mem  = Steel.Memory
module Veq  = Experiment.Steel.VEquiv
module Perm = Learn.Permutation

open Steel.Effect
open Steel.Effect.Atomic
open Experiment.Steel.VPropList


irreducible let __repr_M__ : unit = ()

(*** [repr_steel_t] *)

type pre_t = vprop_list
type post_t (a : Type) = a -> vprop_list

let post_sl_t (#a : Type) (pt : post_t a) : a -> Fl.ty_list
  = fun (x : a) -> vprop_list_sels_t (pt x)

type req_t (pre : pre_t) = sl_f pre -> Type0
type ens_t (pre : pre_t) (a : Type) (post : post_t a) = sl_f pre -> (x : a) -> sl_f (post x) -> Type0

type repr_steel_t (ek : SH.effect_kind) (a : Type)
       (pre : pre_t) (post : post_t a)
       (req : req_t pre) (ens : ens_t pre a post)
  = SH.steel a
      (vprop_of_list pre) (fun x -> vprop_of_list (post x))
      (requires fun h0 -> req (sel pre h0)) (ensures fun h0 x h1 -> ens (sel pre h0) x (sel_f (post x) h1))
      ek

// FIXME: this definition fails when loaded as a dependency but not when lax-checked
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


(*** [spec_r] *)

[@@ Learn.Tactics.Util.__tac_helper__]
noeq inline_for_extraction
type spec_r (a : Type u#a) = {
  spc_pre  : pre_t;
  spc_post : post_t a;
  spc_ro   : vprop_list;
  spc_req  : sl_f spc_pre -> sl_f spc_ro -> Type0;
  spc_ens  : sl_f spc_pre -> (x : a) -> sl_f (spc_post x) -> sl_f spc_ro -> Type0;
}

[@@ Learn.Tactics.Util.__tac_helper__]
let spc_pre1 (#a : Type) (s : spec_r a) : pre_t
  = L.(s.spc_pre @ s.spc_ro)
  
[@@ Learn.Tactics.Util.__tac_helper__]
noextract
let spc_post1 (#a : Type) (s : spec_r a) : post_t a
  = fun x -> L.(s.spc_post x @ s.spc_ro)

type spc_steel_t (ek : SH.effect_kind) (#a : Type) (s : spec_r a)
  =
    SH.steel a
      (      vprop_of_list  s.spc_pre     `star` vprop_of_list s.spc_ro)
      (fun x -> vprop_of_list (s.spc_post x) `star` vprop_of_list s.spc_ro)
      (requires fun h0      -> s.spc_req (sel_f s.spc_pre h0) (sel_f s.spc_ro h0))
      (ensures  fun h0 x h1 -> s.spc_ens (sel_f s.spc_pre h0) x (sel_f (s.spc_post x) h1) (sel_f s.spc_ro h0) /\
                            sel_f s.spc_ro h1 == sel_f s.spc_ro h0)
      ek


type spec_r_exact (#a : Type u#a) (s0 : spec_r a) : (s : spec_r a) -> Type u#(max a 2) =
  | SpecExact : spec_r_exact s0 s0


[@@ Learn.Tactics.Util.__tac_helper__]
noeq
type spec_find_ro (a : Type) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post) = {
  sro_spc     : spec_r a;
  sro_pre_eq  : vequiv_perm L.(sro_spc.spc_pre @ sro_spc.spc_ro) pre;
  sro_post_eq : (x : a) -> vequiv_perm (post x) L.(sro_spc.spc_post x @ sro_spc.spc_ro);
  // sro_spc.spc_req is determined by sr_pre_eq
  sro_req_eq  : (sl0 : sl_f sro_spc.spc_pre) -> (sl_fr0 : sl_f sro_spc.spc_ro) ->
                Lemma (req (extract_vars sro_pre_eq (append_vars sl0 sl_fr0))
                    <==> sro_spc.spc_req sl0 sl_fr0);
  sro_ens_eq  : (sl0 : sl_f sro_spc.spc_pre) -> (sl_fr0 : sl_f sro_spc.spc_ro) ->
                (x : a) -> (sl1 : sl_f (sro_spc.spc_post x)) -> (sl_fr1 : sl_f sro_spc.spc_ro) ->
                Lemma (ens (extract_vars sro_pre_eq (append_vars sl0 sl_fr0))
                         x (extract_vars (Perm.pequiv_sym (sro_post_eq x)) (append_vars sl1 sl_fr1))
                   <==> (sro_spc.spc_ens sl0 x sl1 sl_fr0 /\ sl_fr1 == sl_fr0))
}

[@@ Learn.Tactics.Util.__tac_helper__]
let trivial_spec_find_ro a pre post req ens : spec_find_ro a pre post req ens = {
  sro_spc = Mkspec_r pre post [] (fun sl0 _ -> req sl0) (fun sl0 x sl1 _ -> ens sl0 x sl1);
  sro_pre_eq  = U.cast _ (Perm.pequiv_refl pre);
  sro_post_eq = (fun x -> Perm.pequiv_refl (post x));
  sro_req_eq  = (fun sl0 sl_fr0 -> Fl.nil_uniq sl_fr0);
  sro_ens_eq  = (fun sl0 sl_fr0 x sl1 sl_fr1 -> Fl.nil_uniq sl_fr0; Fl.nil_uniq sl_fr1);
}

inline_for_extraction noextract
val spec_r_of_find_ro
      (#a : Type) (#pre : pre_t) (#post : post_t a) (#req : req_t pre) (#ens : ens_t pre a post)
      (sro : spec_find_ro a pre post req ens)
      (f : repr_steel_t SH.KSteel a pre post req ens)
  : spc_steel_t SH.KSteel sro.sro_spc

inline_for_extraction noextract
val spec_r_of_find_ro_ghost
      (#a : Type) (#pre : pre_t) (#post : post_t a) (#req : req_t pre) (#ens : ens_t pre a post)
      (sro : spec_find_ro a pre post req ens)
      (#opened : Mem.inames) (f : repr_steel_t (SH.KGhost opened) a pre post req ens)
  : spc_steel_t (SH.KGhost opened) sro.sro_spc

(**) private val __end_spec_r_of_find_ro : unit

noeq
type spec_r_steel (#a : Type u#a) (pre : SE.pre_t) (post : SE.post_t a)
                  (req : SE.req_t pre) (ens : SE.ens_t pre a post)
  : (s : spec_r a) -> Type u#(max a 2) =
  | SpecSteel : (tr : to_repr_t a pre post req ens) ->
                (sr : spec_find_ro a tr.r_pre tr.r_post tr.r_req tr.r_ens) ->
                spec_r_steel pre post req ens sr.sro_spc


(*** [prog_tree] *)

/// A tactic taht will be called to solves the goal:
///   [LV.lin_cond env (Tgen a gen_tac gen_c) ?csm ?prd]
/// using [LV.LCgen], unifying [?csm] and [?prd].
type gen_tac_t = Itf.flags_record -> Tactics.Tac unit

noeq
type prog_tree : (a : Type u#a) -> Type u#(max (a+1) 3) =
  // A specification of the subprogram, used to represent function calls
  | Tspec  : (a : Type u#a) -> (sp : spec_r a -> Type u#(max a 2)) ->
             prog_tree a
  // return, with a hint for introducing dependencies on the returned value
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
  // generic combinator
  | Tgen   : (a : Type u#a) -> (gen_tac : gen_tac_t) ->
             (gen_c : (spec_r a -> Type u#(max a 2))) ->
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
  tcs_pre_eq  : Veq.vequiv tcs_pre L.(pre @ tcs_frame);
  tcs_post_eq : (x : a) -> Veq.vequiv L.(post x @ tcs_frame) (tcs_post x)
}

noeq
type tree_cond : (#a : Type u#a) -> (t : prog_tree a) -> (pre : pre_t) -> (post : post_t a) -> Type u#(max (a+1) 3) =
  | TCspec  : (#a : Type u#a) -> (#sp : (spec_r a -> Type u#(max a 2))) ->
              (s : spec_r a) -> (sh : sp s) ->
              (tcs : tree_cond_Spec a (spc_pre1 s) (spc_post1 s)) ->
              tree_cond (Tspec a sp) tcs.tcs_pre tcs.tcs_post
  | TCret   : (#a : Type u#a) -> (#x : a) -> (#sl_hint : post_t a) ->
              (pre : pre_t) -> (post : post_t a) ->
              (p : Veq.vequiv pre (post x)) ->
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
  // We expect the combinator to have a splited read-only frame
  // ALT: only expect a classical {pre,post,req,ens} and use a wrapper to handle the ro frame
  | TCgen   : (#a : Type u#a) -> (#gen_tac : gen_tac_t) ->
              (#gen_c : (spec_r a -> Type u#(max a 2))) ->
              (s : spec_r a) -> (sh : gen_c s) ->
              (pre : pre_t) -> (pre_eq : Veq.vequiv pre (spc_pre1 s)) ->
              (post : post_t a) -> (post_eq : ((x : a) -> Veq.vequiv (spc_post1 s x) (post x))) ->
              tree_cond (Tgen a gen_tac gen_c) pre post


(**** requires / ensures *)

(** spec *)

// ALT? directly express with a bind

let spec_req (#a : Type) (s : spec_r a) (tcs : tree_cond_Spec a (spc_pre1 s) (spc_post1 s))
  : req_t tcs.tcs_pre
  = fun sl0 ->
      tcs.tcs_pre_eq.veq_req sl0 /\
     (forall (sl0' : sl_f s.spc_pre) (sl_ro : sl_f s.spc_ro) (sl_frame : sl_f tcs.tcs_frame) .
      Veq.veq_ens1 tcs.tcs_pre_eq sl0 (append_vars (append_vars sl0' sl_ro) sl_frame) ==>
     (s.spc_req sl0' sl_ro /\
     (forall (x : a) (sl1' : sl_f (s.spc_post x)) . s.spc_ens sl0' x sl1' sl_ro ==>
      (tcs.tcs_post_eq x).veq_req (append_vars (append_vars sl1' sl_ro) sl_frame))))

let spec_ens (#a : Type) (s : spec_r a) (tcs : tree_cond_Spec a (spc_pre1 s) (spc_post1 s))
  : ens_t tcs.tcs_pre a tcs.tcs_post
  = fun sl0 x sl1 ->
    exists (sl0' : sl_f s.spc_pre) (sl1' : sl_f (s.spc_post x))
      (sl_ro : sl_f s.spc_ro) (sl_frame : sl_f tcs.tcs_frame) .
      Veq.veq_ens1 tcs.tcs_pre_eq sl0 (append_vars (append_vars sl0' sl_ro) sl_frame) /\
      s.spc_ens sl0' x sl1' sl_ro /\
      Veq.veq_ens1 (tcs.tcs_post_eq x) (append_vars (append_vars sl1' sl_ro) sl_frame) sl1

(** return *)

let return_req (#pre : pre_t) (#post : vprop_list) (veq : Veq.vequiv pre post) : req_t pre
  = veq.veq_req

let return_ens (#a : Type) (x : a) (#pre : pre_t) (#post : post_t a) (e : Veq.vequiv pre (post x))
  : ens_t pre a post
  = fun sl0 r sl1 ->
      r == x /\ Veq.veq_ens1 e sl0 sl1

(** bind *)

let bind_req (#a : Type)
      (#pre : pre_t) (#itm : post_t a)
      (req_f : req_t pre) (ens_f : ens_t pre a itm)
      (req_g : (x:a) -> req_t (itm x))
  : req_t pre
  = fun sl0 -> req_f sl0 /\
      (forall (x : a) (sl1 : sl_f (itm x)) .
        ens_f sl0 x sl1 ==> req_g x sl1)

/// Unlike the bind combinator of Steel, our ensures clause does not recall the pre-condition of [f] for
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

(** gen *)

/// Similar to spec, but without a frame

let gen_req (#a : Type) (s : spec_r a)
      (#pre : pre_t) (pre_eq : Veq.vequiv pre (spc_pre1 s))
      (#post : post_t a) (post_eq : ((x : a) -> Veq.vequiv (spc_post1 s x) (post x)))
  : req_t pre
  = fun sl0 ->
      pre_eq.veq_req sl0 /\
     (forall (sl0' : sl_f s.spc_pre) (sl_ro : sl_f s.spc_ro) .
      Veq.veq_ens1 pre_eq sl0 (append_vars sl0' sl_ro) ==>
     (s.spc_req sl0' sl_ro /\
     (forall (x : a) (sl1' : sl_f (s.spc_post x)) . s.spc_ens sl0' x sl1' sl_ro ==>
      (post_eq x).veq_req (append_vars sl1' sl_ro))))
      

let gen_ens (#a : Type) (s : spec_r a)
      (#pre : pre_t) (pre_eq : Veq.vequiv pre (spc_pre1 s))
      (#post : post_t a) (post_eq : ((x : a) -> Veq.vequiv (spc_post1 s x) (post x)))
  : ens_t pre a post
  = fun sl0 x sl1 ->
    exists (sl0' : sl_f s.spc_pre) (sl1' : sl_f (s.spc_post x)) (sl_ro : sl_f s.spc_ro) .
      Veq.veq_ens1 pre_eq sl0 (append_vars sl0' sl_ro) /\
      s.spc_ens sl0' x sl1' sl_ro /\
      Veq.veq_ens1 (post_eq x) (append_vars sl1' sl_ro) sl1

(** prog_tree *)

[@@ strict_on_arguments [4]] (* strict on c *)
let rec tree_req (#a : Type u#a) (t : prog_tree a)
                 (#pre : pre_t) (#post : post_t a) (c : tree_cond t pre post)
                 (sl0 : sl_f pre)
  : Tot Type0 (decreases t) =
  match c with
  | TCspec s _ tcs ->
             spec_req s tcs sl0
  | TCret #_ #_  _ _  e ->
             return_req e sl0
  | TCbind #_ #_ #f #g  pre itm _  cf cg ->
             bind_req (tree_req f cf) (tree_ens f cf) (fun x -> tree_req (g x) (cg x)) sl0
  | TCbindP #_ #_ #wp #g  pre _  cg ->
             bind_pure_req wp (fun x -> tree_req (g x) (cg x)) sl0
  | TCif #a #guard  pre _ thn els ->
             ite_req #a guard (tree_req _ thn) (tree_req _ els) sl0
  | TCgen s _  _ pre_eq  _ post_eq ->
              gen_req s pre_eq post_eq sl0

and tree_ens (#a : Type u#a) (t : prog_tree a)
             (#pre : pre_t) (#post : post_t a) (c : tree_cond t pre post)
             (sl0 : sl_f pre) (res : a) (sl1 : sl_f (post res))
  : Tot Type0 (decreases t) =
  match c with
  | TCspec s _  tcs ->
             spec_ens s tcs sl0 res sl1
  | TCret #a #x  _ _  e ->
             return_ens x e sl0 res sl1
  | TCbind #_ #_ #f #g  pre itm post  cf cg ->
             bind_ens (tree_ens f cf) (fun x -> tree_ens (g x) (cg x)) sl0 res sl1
  | TCbindP #_ #_ #wp #g  pre post  cg ->
             bind_pure_ens wp (fun x -> tree_ens (g x) (cg x)) sl0 res sl1
  | TCif #a #guard  pre post thn els ->
             ite_ens #a guard (tree_ens _ thn) (tree_ens _ els) sl0 res sl1
  | TCgen s _  _ pre_eq  _ post_eq ->
              gen_ens s pre_eq post_eq sl0 res sl1


(*** [repr] *)

/// The [repr] type contains a representation of the program as a tree and a corresponding steel function.

noeq inline_for_extraction noextract
type repr (ek : SH.effect_kind) (a : Type) = {
  repr_tree  : prog_tree a;
  repr_steel : (pre : pre_t) -> (post : post_t a) -> (c : tree_cond repr_tree pre post) ->
               repr_steel_t ek a pre post (tree_req repr_tree c) (tree_ens repr_tree c)
}
