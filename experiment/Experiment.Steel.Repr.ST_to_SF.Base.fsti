module Experiment.Steel.Repr.ST_to_SF.Base

module U   = Learn.Util
module L   = FStar.List.Pure
module Ll  = Learn.List
module Fl  = Learn.FList
module Dl  = Learn.DList
module M   = Experiment.Steel.Repr.M
module ST  = Experiment.Steel.Repr.ST

open Experiment.Steel.Repr.ST
open Experiment.Steel.Repr.SF


#set-options "--fuel 1 --ifuel 1"

(* ST.seq_sel_eq written with a conjunction instead of a forall *)
let rec seq_sel_eq_eff_aux (#pre #post : Fl.ty_list) (f_eq : M.veq_eq_t (L.length pre) (L.length post))
                           (sl0 : Fl.flist pre) (sl1 : Fl.flist post) (i : nat)
  : Pure prop (requires M.veq_typ_eq pre post f_eq) (ensures fun _ -> True) (decreases L.length post - i)
  = if i >= L.length post then True
    else match f_eq i with
    | None   -> seq_sel_eq_eff_aux f_eq sl0 sl1 (i+1)
    | Some j -> sl1 i == U.cast _ (sl0 j) /\ seq_sel_eq_eff_aux f_eq sl0 sl1 (i+1)

let seq_sel_eq_eff (#pre #post : Fl.ty_list) (f_eq : M.veq_eq_t (L.length pre) (L.length post))
                   (sl0 : Fl.flist pre) (sl1 : Fl.flist post)
  : Pure prop (requires M.veq_typ_eq pre post f_eq) (ensures fun _ -> True)
  = seq_sel_eq_eff_aux f_eq sl0 sl1 0

val seq_sel_eq_eff_sound
      (#pre #post : Fl.ty_list) (f_eq : M.veq_eq_t (L.length pre) (L.length post))
      (sl0 : Fl.flist pre) (sl1 : Fl.flist post)
  : Lemma (requires M.veq_typ_eq pre post f_eq)
          (ensures  seq_sel_eq_eff f_eq sl0 sl1 <==> ST.seq_sel_eq f_eq sl0 sl1)


[@@ strict_on_arguments [3]] (* strict on t *)
let rec repr_SF_of_ST
      (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
      (t : ST.prog_tree a pre post) (sl0 : Fl.flist pre)
  : Tot (prog_tree a post) (decreases t)
  = match t with
  | ST.Tequiv pre post0 e ->
          // TODO? specialized constructor / wp
          Tspec U.unit' (const_post post0) (e.seq_req sl0)
                (fun _ sl1 -> seq_sel_eq_eff e.seq_eq sl0 sl1 /\ e.seq_ens sl0 sl1)
  | ST.Tframe a pre post frame f ->
          let (sl0', sl_frame) = Fl.splitAt_ty pre frame sl0 in
          Tbind a a _ _ (repr_SF_of_ST f sl0') (fun x sl1' ->
          Tret a x (frame_post post frame) (Fl.dlist_of_f (Fl.append sl1' sl_frame)))
  | ST.Tspec a pre post req ens ->
          Tspec a post (req sl0) (ens sl0)
  | ST.Tret a x post ->
          Tret a x post (Fl.dlist_of_f sl0)
  | ST.Tbind a b pre itm post f g ->
          Tbind a b  _ _ (repr_SF_of_ST f sl0) (fun x sl1 -> repr_SF_of_ST (g x) sl1)
  | ST.TbindP a b pre post wp g ->
          TbindP a b _ wp (fun x -> repr_SF_of_ST (g x) sl0)
  | ST.Tif a guard pre post thn els ->
          Tif a guard post (repr_SF_of_ST thn sl0) (repr_SF_of_ST els sl0)

[@@ strict_on_arguments [2]] (* strict on t *)
let rec shape_SF_of_ST
      (#pre_n #post_n : nat) (t : ST.shape_tree pre_n post_n)
  : Tot (shape_tree post_n) (decreases t)
  = match t with
  | ST.Sequiv _ post_n _ ->
          Sspec post_n
  | ST.Sframe pre_n post_n frame_n s_f ->
          Sbind _ _ (shape_SF_of_ST s_f) (Sret true (post_n + frame_n))
  | ST.Sspec pre_n post_n ->
          Sspec post_n
  | ST.Sret smp_ret n ->
          Sret smp_ret n
  | ST.Sbind pre_n itm_n post_n s_f s_g ->
          Sbind _ _ (shape_SF_of_ST s_f) (shape_SF_of_ST s_g)
  | ST.SbindP pre_n post_n s_g ->
          SbindP _ (shape_SF_of_ST s_g)
  | ST.Sif pre_n post_n s_thn s_els ->
          Sif _ (shape_SF_of_ST s_thn) (shape_SF_of_ST s_els)


(*** Soundness *)

val repr_SF_of_ST_req
      (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
      (t : ST.prog_tree a pre post)
      (sl0 : Fl.flist pre)
  : Lemma (ST.tree_req t sl0 <==> tree_req (repr_SF_of_ST t sl0))

val repr_SF_of_ST_ens
      (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
      (t : ST.prog_tree a pre post)
      (sl0 : Fl.flist pre) (res : a) (sl1 : Fl.flist (post res))
  : Lemma (ST.tree_ens t sl0 res sl1 <==> tree_ens (repr_SF_of_ST t sl0) res sl1)

val repr_SF_of_ST_shape
      (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
      (t : ST.prog_tree a pre post)
      (#post_n : nat) (s : ST.shape_tree (L.length pre) post_n)
      (sl0 : Fl.flist pre)
  : Lemma (requires ST.prog_has_shape t s)
          (ensures  prog_has_shape (repr_SF_of_ST t sl0) (shape_SF_of_ST s))
