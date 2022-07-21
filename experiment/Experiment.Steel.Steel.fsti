module Experiment.Steel.Steel

module U   = Learn.Util
module T   = FStar.Tactics
module Mem = Steel.Memory

include Experiment.Steel.SteelHack

open Steel.Effect
open Steel.Effect.Atomic


val focus_rmem_feq (p q r : vprop) (h : rmem p)
  : Lemma (requires can_be_split p q /\ can_be_split q r)
          (ensures  can_be_split p r /\ focus_rmem h q r == h r)

val focus_rmem_trans (p q r : vprop) (h : rmem p)
  : Lemma (requires can_be_split p q /\ can_be_split q r)
          (ensures  can_be_split p r /\ focus_rmem (focus_rmem h q) r == focus_rmem h r)

val focus_rmem_mkrmem (p q : vprop) (h : hmem p)
  : Lemma (requires can_be_split p q)
          (ensures  Mem.interp (hp_of q) h /\ focus_rmem (mk_rmem p h) q == mk_rmem q h)


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
    forall (h0 : hmem pre_g) . (let h0 = mk_rmem pre_g h0 in
     (**) equiv_can_be_split pre_g pre_f; (
     req_g h0 ==>
      (req_f (focus_rmem h0 pre_f) /\
      (forall (x : a) (h1 : hmem (post_g x)) . (let h1 = mk_rmem (post_g x) h1 in
        (**) eq_post x; equiv_can_be_split (post_g x) (post_f x); (
        ens_f (focus_rmem h0 pre_f) x (focus_rmem h1 (post_f x)) ==>
        ens_g h0 x h1))))))

val intro_subcomp_no_frame_pre
      (#a:Type)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
      (s_pre :  (h0 : hmem pre_g) -> Lemma
         (requires can_be_split pre_g pre_f /\
                   Mem.interp (hp_of pre_f) h0 /\
                   req_g (mk_rmem pre_g h0))
         (ensures  req_f (mk_rmem pre_f h0)))
      (s_post : (h0 : hmem pre_g) -> (x : a) -> (h1 : hmem (post_g x)) -> Lemma
         (requires can_be_split pre_g pre_f /\ can_be_split (post_g x) (post_f x) /\
                   Mem.interp (hp_of pre_f) h0 /\ Mem.interp (hp_of (post_f x)) h1 /\
                   req_g (mk_rmem pre_g h0) /\ req_f (mk_rmem pre_f h0) /\
                   ens_f (mk_rmem pre_f h0) x (mk_rmem (post_f x) h1))
         (ensures  ens_g (mk_rmem pre_g h0) x (mk_rmem (post_g x) h1)))
  : squash (subcomp_no_frame_pre req_f ens_f req_g ens_g eq_pre eq_post)

inline_for_extraction noextract
val unit_steel_subcomp_no_frame
      (#a : Type)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
      (sb_pre : squash (subcomp_no_frame_pre req_f ens_f req_g ens_g eq_pre eq_post))
      ($f : unit_steel a pre_f post_f req_f ens_f)
  : unit_steel a pre_g post_g req_g ens_g

inline_for_extraction noextract
val unit_steel_ghost_subcomp_no_frame
      (#a : Type) (#opened : Mem.inames)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
      (sb_pre : squash (subcomp_no_frame_pre req_f ens_f req_g ens_g eq_pre eq_post))
      ($f : unit_steel_ghost a opened pre_f post_f req_f ens_f)
  : unit_steel_ghost a opened pre_g post_g req_g ens_g


noeq
type effect_kind =
  | KSteel
  | KAtomic of Mem.inames
  // Informative Ghost
  | KGhostI of Mem.inames
  | KGhost  of Mem.inames

noeq inline_for_extraction
type steel (a : Type) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
  : effect_kind -> Type =
  | FSteel  : (f : unit_steel a pre post req ens) ->
               steel a pre post req ens KSteel
  | FAtomic : (o : Mem.inames) -> (f : unit_steel_atomic a o pre post req ens) ->
               steel a pre post req ens (KAtomic o)
  | FGhostI : (o : Mem.inames) -> (f : unit_steel_ghostI a o pre post req ens) ->
               steel a pre post req ens (KGhostI o)
  | FGhost  : (o : Mem.inames) -> (f : unit_steel_ghost  a o pre post req ens) ->
               steel a pre post req ens (KGhost o)

unfold inline_for_extraction
let steel_u #a #pre #post #req #ens (f : steel a pre post req ens KSteel)
  : unit_steel a pre post req ens
  = FSteel?.f f

unfold inline_for_extraction
let steel_f #a #pre #post #req #ens (f : unit_steel a pre post req ens)
  : steel a pre post req ens KSteel
  = FSteel f

unfold inline_for_extraction
let atomic_u #opened #a #pre #post #req #ens (f : steel a pre post req ens (KAtomic opened))
  : unit_steel_atomic a opened pre post req ens
  = U.cast _ (FAtomic?.f f)

unfold inline_for_extraction
let atomic_f #opened #a #pre #post #req #ens (f : unit_steel_atomic a opened pre post req ens)
  : steel a pre post req ens (KAtomic opened)
  = FAtomic opened f

unfold inline_for_extraction
let ghost_u #opened #a #pre #post #req #ens (f : steel a pre post req ens (KGhost opened))
  : unit_steel_ghost a opened pre post req ens
  = U.cast (unit_steel_ghost a opened pre post req ens) (FGhost?.f f)

unfold inline_for_extraction
let ghost_f #opened #a #pre #post #req #ens (f : unit_steel_ghost a opened pre post req ens)
  : steel a pre post req ens (KGhost opened)
  = FGhost opened f

unfold inline_for_extraction
let ghostI_u #opened #a #pre #post #req #ens (f : steel a pre post req ens (KGhostI opened))
  : unit_steel_ghostI a opened pre post req ens
  = U.cast (unit_steel_ghostI a opened pre post req ens) (FGhostI?.f f)

unfold inline_for_extraction
let ghostI_f #opened #a #pre #post #req #ens (f : unit_steel_ghostI a opened pre post req ens)
  : steel a pre post req ens (KGhostI opened)
  = FGhostI opened f
