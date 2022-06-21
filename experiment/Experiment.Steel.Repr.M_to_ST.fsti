module Experiment.Steel.Repr.M_to_ST

module L   = FStar.List.Pure
module M   = Experiment.Steel.Repr.M
module Veq = Experiment.Steel.VEquiv

open Experiment.Steel.VPropList
open Experiment.Steel.Repr.M
open Steel.Effect.Common
open Experiment.Steel.Repr.ST

(*** Repr.M --> Repr.ST *)

let sequiv_of_vequiv (#pre #post : vprop_list) (e : Veq.vequiv pre post)
  : sequiv (vprop_list_sels_t pre) (vprop_list_sels_t post)
  = {
  seq_req = e.veq_req;
  seq_ens = e.veq_ens;
  seq_eq  = Veq.veq_eq_sl (Veq.veq_of_list e.veq_eq);
  seq_typ = e.veq_typ
}

let repr_ST_of_M_Spec
      (a : Type) (pre : M.pre_t) (post : M.post_t a) (req : M.req_t pre) (ens : M.ens_t pre a post)
      (tcs : tree_cond_Spec a pre post)
  : prog_tree a (vprop_list_sels_t tcs.tcs_pre) (post_sl_t tcs.tcs_post)
  =
    Tequiv (vprop_list_sels_t tcs.tcs_pre)
           (vprop_list_sels_t L.(pre @ tcs.tcs_frame))
           (sequiv_of_vequiv tcs.tcs_pre_eq);;
    (**) L.map_append Mkvprop'?.t pre tcs.tcs_frame;
    x <-- Tframe a (vprop_list_sels_t pre) (post_sl_t post) (vprop_list_sels_t tcs.tcs_frame)
        (Tspec a (vprop_list_sels_t pre) (post_sl_t post) req ens);
    (**) L.map_append Mkvprop'?.t (post x) tcs.tcs_frame;
    Tequiv (vprop_list_sels_t L.(post x @ tcs.tcs_frame))
           (vprop_list_sels_t (tcs.tcs_post x))
           (sequiv_of_vequiv (tcs.tcs_post_eq x));;
    Tret _ x (post_sl_t tcs.tcs_post)

[@@ strict_on_arguments [4]] (* strict on c *)
let rec repr_ST_of_M (#a : Type) (t : M.prog_tree u#a a)
                     (#pre0 : M.pre_t) (#post0 : M.post_t a) (c : M.tree_cond t pre0 post0)
  : Tot (prog_tree a (vprop_list_sels_t pre0) (post_sl_t post0))
        (decreases t)
  = match c with
  | TCspec #a #pre #post #req #ens  tcs ->
             repr_ST_of_M_Spec a pre post req ens tcs
  | TCspecS #a tr tcs ->
             repr_ST_of_M_Spec a tr.r_pre tr.r_post tr.r_req tr.r_ens tcs
  | TCret #a #x #_  pre post  e ->
             Tequiv (vprop_list_sels_t pre) (vprop_list_sels_t (post x)) (sequiv_of_vequiv e);;
             Tret _ x (post_sl_t post)
  | TCbind #a #b #f #g  pre itm post  cf cg ->
             x <-- repr_ST_of_M f cf;
             repr_ST_of_M (g x) (cg x)
  | TCbindP #a #b #wp #g  pre post  cg ->
             TbindP a b _ _ wp (fun x -> repr_ST_of_M (g x) (cg x))
  | TCif #a #guard #thn #els pre post cthn cels ->
             Tif a guard _ _ (repr_ST_of_M thn cthn) (repr_ST_of_M els cels)

[@@ strict_on_arguments [2]] (* strict on s *)
let rec shape_ST_of_M (#pre_n : nat) (#post_n : nat) (s : M.shape_tree pre_n post_n)
  : Tot (shape_tree pre_n post_n) (decreases s)
  = match s with
  | M.Sspec pre_n post_n pre'_n post'_n frame_n p0 p1 ->
        Sbind _ _ _ (Sequiv pre'_n (pre_n  + frame_n) (Veq.veq_of_list p0)) (
        Sbind _ _ _ (Sframe pre_n post_n frame_n (Sspec  pre_n post_n)) (
        Sbind _ _ _ (Sequiv (post_n + frame_n) post'_n (Veq.veq_of_list p1))
                    (Sret   true post'_n)))
  | M.Sret pre_n post_n p ->
        Sbind _ _ _ (Sequiv pre_n post_n (Veq.veq_of_list p)) (Sret false post_n)
  | M.Sbind _ _ _ f g -> Sbind  _ _ _ (shape_ST_of_M f) (shape_ST_of_M g)
  | M.SbindP _ _ g    -> SbindP _ _ (shape_ST_of_M g)
  | M.Sif _ _ thn els -> Sif _ _ (shape_ST_of_M thn) (shape_ST_of_M els)
                    


(*** Soundness *)

val repr_ST_of_M_req (#a : Type) (t : M.prog_tree u#a a)
                     (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
                     (sl0 : sl_f pre)
  : Lemma (M.tree_req t c sl0 <==> tree_req (repr_ST_of_M t c) sl0)

val repr_ST_of_M_ens (#a : Type) (t : M.prog_tree u#a a)
                     (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
                     (sl0 : sl_f pre) (res : a) (sl1 : sl_f (post res))
  : Lemma (M.tree_ens t c sl0 res sl1 <==> tree_ens (repr_ST_of_M t c) sl0 res sl1)


val repr_ST_of_M_shape
      (#a : Type) (t : M.prog_tree u#a a)
      (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
      (#post_n : nat) (s : M.shape_tree (L.length pre) post_n)
   : Lemma (requires M.tree_cond_has_shape c s)
           (ensures  prog_has_shape (repr_ST_of_M t c) (shape_ST_of_M s))
