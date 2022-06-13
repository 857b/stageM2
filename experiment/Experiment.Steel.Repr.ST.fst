module Experiment.Steel.Repr.ST

module L = FStar.List.Pure
module T = FStar.Tactics

open FStar.Tactics
open FStar.Calc


(***** [equiv] *)

#push-options "--ifuel 0"

let intro_equiv (#a : Type) (#pre : pre_t) (#post : post_t a) (f g : prog_tree a pre post)
    (eq_req : (sl0 : Fl.flist pre) -> squash (tree_req f sl0 <==> tree_req g sl0))
    (eq_ens : (sl0 : Fl.flist pre) -> (res : a) -> (sl1 : Fl.flist (post res)) ->
              (_ : squash (tree_req f sl0 /\ tree_req f sl0)) ->
              squash (tree_ens f sl0 res sl1 <==> tree_ens g sl0 res sl1))
    : squash (equiv f g)
    = FStar.Classical.forall_intro_squash_gtot eq_req;
      introduce forall (sl0 : Fl.flist pre) (res : a) (sl1 : Fl.flist (post res)).
              tree_req f sl0 ==> (tree_ens f sl0 res sl1 <==> tree_ens g sl0 res sl1)
        with introduce _ ==> _ with _ . (eq_req sl0; eq_ens sl0 res sl1 ())

let equiv_Tframe #a #pre #post frame f f' eq_f
  = _ by T.(norm [delta_only [`%equiv; `%tree_req; `%tree_ens]; iota; zeta];
            smt ())

let equiv_Tbind #a #b #pre #itm #post f f' g g' eq_f eq_g
  = let eq_g = FStar.Classical.forall_intro_squash_gtot eq_g in
    _ by T.(norm [delta_only [`%equiv; `%tree_req; `%tree_ens]; iota; zeta];
            smt ())

let equiv_TbindP #a #b #pre #post wp g g' eq_g
  =
    FStar.Classical.forall_intro_squash_gtot eq_g;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    assert (equiv (TbindP a b pre post wp g) (TbindP a b pre post wp g'))
      by T.(norm [delta_only [`%equiv; `%tree_req; `%tree_ens]; iota; zeta];
            smt ())

let equiv_Tif #a guard #pre #post thn thn' els els' eq_thn eq_els
  = _ by T.(norm [delta_only [`%equiv; `%tree_req; `%tree_ens]; iota; zeta];
            smt ())

let equiv_Tbind_assoc_Tbind #a #b #c #pre #itm0 #itm1 #post f g h
  : squash (equiv (bind (bind f g) h) (bind f (fun x -> bind (g x) h)))
  = _ by T.(norm [delta_only [`%equiv; `%tree_req; `%tree_ens; `%bind]; iota; zeta];
            smt ())

#pop-options

(**) let __begin_shape = ()

(*** Binders flattening *)

#push-options "--fuel 2 --ifuel 1"
let rec flatten_equiv
      #a #pre #post (t : prog_tree u#a u#b a pre post)
  : Lemma (ensures equiv (flatten_prog t) t) (decreases %[t; 1])
  = flatten_equiv_aux t flatten_prog_k_id
      (fun _ _ _ -> ()) (fun _ _ _ _ _ -> ())

and flatten_equiv_aux
      #a  #pre #post (t : prog_tree u#a u#b a pre post)
      #a1 #post1 (k : ((#pre' : pre_t) -> (t' : prog_tree a pre' post) -> prog_tree a1 pre' post1))
      (k_equiv : (pre' : pre_t) -> (t'0 : prog_tree a pre' post) -> (t'1 : prog_tree a pre' post) ->
                     Lemma (requires equiv t'0 t'1) (ensures equiv (k t'0) (k t'1)))
      (k_bind  : ((a0 : Type u#a) -> (pre' : pre_t) -> (itm : post_t a0) ->
                      (f : prog_tree a0 pre' itm) -> (g : ((x : a0) -> (prog_tree a (itm x) post))) ->
                     Lemma (equiv (k (Tbind a0 a pre' itm post f g))
                                  (Tbind a0 a1 pre' itm post1 f (fun x -> k (g x))))))
  : Lemma (ensures equiv (flatten_prog_aux t k) (k t)) (decreases %[t; 0])
  = match t with
  | Tequiv _ _ _ | Tspec _ _ _ _ _ | Tret _ _ _ -> ()
  | Tframe a pre post frame f ->
             equiv_Tframe frame (flatten_prog f) f (flatten_equiv f);
             k_equiv _ (Tframe _ _ _ frame (flatten_prog f)) t
  | Tbind  a b pre itm post f g ->
             let t = Tbind a b pre itm post f g in
             let g1 (x : a) = flatten_prog_aux (g x) k in
             let g2 (x : a) = k (g x) in
             let k1 (#pre' : pre_t) (f' : prog_tree a pre' itm) =
               Tbind a a1 pre' itm post1 f' g1
             in
             assert (flatten_prog_aux t k == flatten_prog_aux f k1)
               by T.(trefl ());
             flatten_equiv_aux f k1
               (fun _ t'0 t'1 -> equiv_Tbind t'0 t'1 g1 g1 () (fun _ -> ()))
               (fun a0 pre' itm f' g' -> equiv_Tbind_assoc_Tbind f' g' g1);
             equiv_Tbind f f g1 g2
               () (fun (x : a) -> flatten_equiv_aux (g x) k k_equiv k_bind);
             assert (equiv (flatten_prog_aux t k) (Tbind a a1 pre itm post1 f g2));
             k_bind _ _ _ f g
  | TbindP a b pre post wp g ->
             let t = TbindP a b pre post wp g in
             let g1 (x : a) = flatten_prog (g x) in
             assert (flatten_prog_aux t k == k (TbindP _ _ _ _ wp g1))
               by T.(trefl ());
             equiv_TbindP wp g1 g
               (fun x -> flatten_equiv (g x));
             k_equiv _ (TbindP _ _ _ _ wp g1) t
  | Tif a guard pre post thn els ->
             equiv_Tif guard (flatten_prog thn) thn (flatten_prog els) els
                       (flatten_equiv thn) (flatten_equiv els);
             k_equiv _ (Tif a guard pre post (flatten_prog thn) (flatten_prog els)) t

let rec flatten_prog_shape
      #a #pre #post (t : prog_tree u#a u#b a pre post)
      (#post_n : nat) (s : shape_tree (L.length pre) post_n)
   : Lemma (requires prog_has_shape t s)
           (ensures  prog_has_shape (flatten_prog t) (flatten_shape s))
           (decreases %[t; 1])
   = flatten_prog_shape_aux t s flatten_prog_k_id post_n flatten_shape_k_id (fun _ _ _ -> ())

and flatten_prog_shape_aux
      #a #pre #post (t : prog_tree u#a u#b a pre post)
      (#post_n : nat) (s : shape_tree (L.length pre) post_n)
      #a1 #post1 (k_t : ((#pre' : pre_t) -> (t' : prog_tree a pre' post) -> prog_tree u#a u#b a1 pre' post1))
      (post1_n : nat {post_has_len post1 post1_n})
      (k_s : ((#pre'_n : nat) -> (s' : shape_tree pre'_n post_n) -> shape_tree pre'_n post1_n))
      (k_hyp : (pre' : pre_t) -> (t' : prog_tree a pre' post) -> (s' : shape_tree (L.length pre') post_n) ->
                   Lemma (requires prog_has_shape t' s') (ensures prog_has_shape (k_t t') (k_s s')))
   : Lemma (requires prog_has_shape t s)
           (ensures  prog_has_shape (flatten_prog_aux t k_t) (flatten_shape_aux s k_s))
           (decreases %[t; 0])
   = match t with
  | Tequiv _ _ _ | Tspec _ _ _ _ _ | Tret _ _ _ ->
           k_hyp _ t s
  | Tframe a pre post frame f ->
           let Sframe _ _ frame_n s_f = s in
           flatten_prog_shape f s_f;
           k_hyp _ (Tframe _ _ _ frame (flatten_prog f))
                   (Sframe _ _ frame_n (flatten_shape s_f))
  | Tbind  a b pre itm post f g ->
           let t = Tbind a b pre itm post f g in
           let Sbind pre_n itm_n post_n s_f s_g = s in
           let s = Sbind pre_n itm_n post_n s_f s_g in
           let g1 (x : a) = flatten_prog_aux (g x) k_t in
           let k_t1 (#pre' : pre_t) (f' : prog_tree a pre' itm) =
             Tbind a a1 pre' itm post1 f' g1
           in let k_s1 (#pre'_n : nat) (s_f' : shape_tree pre'_n itm_n) =
             Sbind _ itm_n _ s_f' (flatten_shape_aux s_g k_s)
           in
           assert (flatten_prog_aux t k_t == flatten_prog_aux f k_t1)
             by T.(trefl ());
           assert (flatten_shape_aux s k_s == flatten_shape_aux s_f k_s1)
             by T.(trefl ());
           flatten_prog_shape_aux f s_f k_t1 post1_n k_s1
             (fun pre' t' s' ->
               introduce forall (x : a) . prog_has_shape (g1 x) (flatten_shape_aux s_g k_s)
                 with flatten_prog_shape_aux (g x) s_g k_t post1_n k_s k_hyp)
  | TbindP a b pre post wp g ->
           let t = TbindP a b pre post wp g in
           let SbindP _ _ s_g = s in
           let g1 (x : a) = flatten_prog (g x) in
           assert (flatten_prog_aux t k_t == k_t (TbindP _ _ _ _ wp g1))
             by T.(trefl ());
           introduce forall (x : a) . prog_has_shape (g1 x) (flatten_shape s_g)
             with flatten_prog_shape (g x) s_g;
           k_hyp _ (TbindP _ _ _ _ wp g1) (SbindP _ _ (flatten_shape s_g))
  | Tif a guard pre post thn els ->
           let Sif _ _ s_thn s_els = s in
           flatten_prog_shape thn s_thn;
           flatten_prog_shape els s_els;
           k_hyp _ (Tif a guard pre post (flatten_prog thn) (flatten_prog els))
                   (Sif _ _ (flatten_shape s_thn) (flatten_shape s_els))

#pop-options
