module Experiment.Steel.SteelHack

module Mem = Steel.Memory

open Steel.Effect
open Steel.Effect.Atomic


type unit_steel (a : Type) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
  = unit -> Steel a pre post req ens

// ALT? merge atomic and ghostI
let unit_steel_atomic
      (a : Type) (opened : Mem.inames) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
  = unit -> SteelAtomic a opened pre post req ens

let unit_steel_ghostI
      (a : Type) (opened : Mem.inames) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
  = unit -> SteelAtomicBase a false opened Unobservable pre post req ens

let unit_steel_ghost
      (a : Type) (opened : Mem.inames) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
  = unit -> SteelGhost a opened pre post req ens


/// [subcomp_pre] without [rewrite_with_tactic] and [frame_equality] reduced
let subcomp_pre' (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (#frame:vprop)
  (#pr:prop)
  (_:squash (can_be_split_dep pr pre_g (pre_f `star` frame)))
  (_:squash (equiv_forall post_g (fun x -> post_f x `star` frame)))
  : pure_pre
= squash (
  (forall (h0:hmem pre_g). req_g (mk_rmem pre_g h0) ==> pr /\
    (can_be_split_trans pre_g (pre_f `star` frame) pre_f;
    req_f (focus_rmem (mk_rmem pre_g h0) pre_f))) /\
  (forall (h0:hmem pre_g) (x:a) (h1:hmem (post_g x)). (
     pr ==> (
     can_be_split_trans (post_g x) (post_f x `star` frame) (post_f x);
     can_be_split_trans (pre_g) (pre_f `star` frame) frame;
     can_be_split_trans (post_g x) (post_f x `star` frame) frame;
     can_be_split_trans pre_g (pre_f `star` frame) pre_f;

     (req_g (mk_rmem pre_g h0) /\
      ens_f (focus_rmem (mk_rmem pre_g h0) pre_f) x (focus_rmem (mk_rmem (post_g x) h1) (post_f x)) /\
      (*
      frame_equalities frame
        (focus_rmem (mk_rmem pre_g h0) frame)
        (focus_rmem (mk_rmem (post_g x) h1) frame)*)
      sel_of frame
        (let _ = can_be_split_interp pre_g (pre_f `star` frame) h0 in h0) ==
      sel_of frame
        (let _ = can_be_split_interp (post_g x) (post_f x `star` frame) h1 in h1)
     )
        ==> ens_g (mk_rmem pre_g h0) x (mk_rmem (post_g x) h1))
  ))
)

val intro_subcomp_pre'
  (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (#frame:vprop)
  (#pr:prop)
  (p1:squash (can_be_split_dep pr pre_g (pre_f `star` frame)))
  (p2:squash (equiv_forall post_g (fun x -> post_f x `star` frame)))
  (s_pr   : (h0:hmem pre_g) -> Lemma
     (requires req_g (mk_rmem pre_g h0))
     (ensures  pr))
  (s_pre  : (h0:hmem pre_g) -> Lemma
     (requires req_g (mk_rmem pre_g h0) /\ pr /\
               can_be_split pre_g pre_f)
     (ensures  req_f (focus_rmem (mk_rmem pre_g h0) pre_f)))
  (s_post : (h0:hmem pre_g) -> (x:a) -> (h1:hmem (post_g x)) -> Lemma
     (requires req_g (mk_rmem pre_g h0) /\ pr /\
               can_be_split pre_g pre_f /\
               can_be_split (post_g x) (post_f x) /\
               Mem.interp (hp_of frame) h0 /\
               Mem.interp (hp_of frame) h1 /\
               ens_f (focus_rmem (mk_rmem pre_g h0) pre_f) x (focus_rmem (mk_rmem (post_g x) h1) (post_f x)) /\
               sel_of frame h0 == sel_of frame h1)
     (ensures  ens_g (mk_rmem pre_g h0) x (mk_rmem (post_g x) h1)))
  : subcomp_pre' req_f ens_f req_g ens_g p1 p2


inline_for_extraction noextract
val steel_subcomp (a:Type)
  (pre_f:pre_t)       (post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (pre_g:pre_t)       (post_g:post_t a)
  (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (frame:vprop)
  (pr : prop)
  (p1 : squash (can_be_split_dep pr pre_g (pre_f `star` frame)))
  (p2 : squash (equiv_forall post_g (fun x -> post_f x `star` frame)))
  (sc : squash (subcomp_pre' req_f ens_f req_g ens_g p1 p2))
  ($f : unit_steel a pre_f post_f req_f ens_f)
  : unit_steel a pre_g post_g req_g ens_g

inline_for_extraction noextract
val steel_ghost_subcomp (a:Type) (opened : Mem.inames)
  (pre_f:pre_t)       (post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (pre_g:pre_t)       (post_g:post_t a)
  (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (frame:vprop)
  (pr : prop)
  (p1 : squash (can_be_split_dep pr pre_g (pre_f `star` frame)))
  (p2 : squash (equiv_forall post_g (fun x -> post_f x `star` frame)))
  (sc : squash (subcomp_pre' req_f ens_f req_g ens_g p1 p2))
  ($f : unit_steel_ghost a opened pre_f post_f req_f ens_f)
  : unit_steel_ghost a opened pre_g post_g req_g ens_g
