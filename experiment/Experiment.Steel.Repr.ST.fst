module Experiment.Steel.Repr.ST

module L = FStar.List.Pure
module T = FStar.Tactics
open FStar.Calc


(***** [equiv] *)

#push-options "--ifuel 0"

let equiv_Tframe #a #pre #post frame f f' eq_f
  = _ by T.(//unfold one level of tree_ens / tree_req
            norm [delta_only [`%equiv; `%tree_req; `%tree_ens]; zeta];
            norm [iota];
            smt ())

let equiv_Tbind #a #b #pre #itm #post f f' g g' eq_f eq_g
  = let eq_g = FStar.Classical.forall_intro_squash_gtot eq_g in
    _ by T.(norm [delta_only [`%equiv; `%tree_req; `%tree_ens]; zeta];
            norm [iota];
            smt ())

let equiv_TbindP #a #b #pre #post wp f g g' eq_g
  =
    FStar.Classical.forall_intro_squash_gtot eq_g;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    assert (equiv (TbindP a b pre post wp f g) (TbindP a b pre post wp f g'))
      by T.(norm [delta_only [`%equiv; `%tree_req; `%tree_ens]; zeta];
            norm [iota];
            smt ())

let equiv_Tbind_assoc_Tbind #a #b #c #pre #itm0 #itm1 #post f g h
  : squash (equiv (bind (bind f g) h) (bind f (fun x -> bind (g x) h)))
  = _ by T.(norm [delta_only [`%equiv; `%tree_req; `%tree_ens; `%bind]; zeta];
            norm [iota];
            smt ())

#pop-options

(**) let __begin_shape = ()

(**** soundness of M --> ST *)

(***** Spec *)

let norm_tree_spec () : T.Tac unit
  = T.norm [delta_only [`%repr_ST_of_M; `%post_ST_of_M; `%bind; `%tree_req; `%tree_ens; `%const_post];
            delta_attr [`%U.__util_func__];
            delta_qualifier ["unfold"];
            zeta; iota; simplify]

#push-options "--z3rlimit 15 --ifuel 1"
let repr_ST_of_M__TCspec_ens
      #a #pre #post (req : M.req_t pre) (ens : M.ens_t pre a post)
      (pre' : M.pre_t) (post' : M.post_t a) (frame : vprop_list)
      (p0 : vequiv pre' L.(pre @ frame)) (p1 : (x : a) -> vequiv (post x @ frame) (post' x))
      (sl0' : sl_f pre') (res : a) (sl1' : sl_f (post' res))

  : Lemma (
    (**) L.map_append Mkvprop'?.t pre frame;
    (**) L.map_append Mkvprop'?.t (post res) frame;

    (tree_ens (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1)) sl0' res sl1'
    <==> (let sl0, frame0 = Fl.splitAt_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                             (Fl.apply_pequiv (vequiv_sl p0) sl0') in
        let sl1, frame1 = Fl.splitAt_ty (vprop_list_sels_t (post res)) (vprop_list_sels_t frame)
                             (Fl.apply_pequiv (Perm.pequiv_sym (vequiv_sl (p1 res))) sl1') in
        frame1 == frame0 /\ ens sl0 res sl1)))
  =
    L.map_append Mkvprop'?.t pre frame;
    L.map_append Mkvprop'?.t (post res) frame;
    assert (
      tree_ens (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1)) sl0' res sl1'
    <==> (exists (sl1f : Fl.flist L.(vprop_list_sels_t (post res) @ vprop_list_sels_t frame)) .
          let sl0, frame0 = Fl.splitAt_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                               (Fl.apply_pequiv (vequiv_sl p0) sl0') in
          let sl1, frame1 = Fl.splitAt_ty (vprop_list_sels_t (post res)) (vprop_list_sels_t frame) sl1f in
          sl1' == Fl.apply_pequiv (vequiv_sl (p1 res)) sl1f /\
          frame1 == frame0 /\ ens sl0 res sl1))
      by T.(norm_tree_spec (); smt ());

    introduce forall (sl1f : Fl.flist L.(vprop_list_sels_t (post res) @ vprop_list_sels_t frame)) .
        sl1' == Fl.apply_pequiv (vequiv_sl (p1 res)) sl1f <==>
        sl1f == Fl.apply_pequiv (Perm.pequiv_sym (vequiv_sl (p1 res))) sl1'
      with Fl.apply_pequiv_sym_eq_iff (vequiv_sl (p1 res)) sl1f sl1';

    assert (tree_ens (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1)) sl0' res sl1'
    <==> (let sl0, frame0 = Fl.splitAt_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                             (Fl.apply_pequiv (vequiv_sl p0) sl0') in
        let sl1, frame1 = Fl.splitAt_ty (vprop_list_sels_t (post res)) (vprop_list_sels_t frame)
                             (Fl.apply_pequiv (Perm.pequiv_sym (vequiv_sl (p1 res))) sl1') in
        frame1 == frame0 /\ ens sl0 res sl1))
#pop-options


#push-options "--z3rlimit 30 --ifuel 1"
let rec repr_ST_of_M_req (#a : Type) (t : M.prog_tree a)
                         (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
                         (sl0 : sl_f pre)
  : Lemma (ensures M.tree_req t c sl0 <==> tree_req (repr_ST_of_M t c) sl0)
          (decreases t)
  = match c as c returns squash (M.tree_req t c sl0 <==> tree_req (repr_ST_of_M t c) sl0) with
  | TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1 ->
             L.map_append Mkvprop'?.t pre frame;

             calc (<==>) {
               M.tree_req _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1) sl0;
             <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ()) }
               req (extract_vars_f pre' pre frame p0 sl0)._1;
             <==> { assert_norm (extract_vars_f pre' pre frame p0 sl0
                    == Fl.splitAt_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                         (Fl.apply_pequiv (vequiv_sl p0) sl0)) }
               req (Fl.splitAt_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                              (Fl.apply_pequiv (vequiv_sl p0) sl0))._1;
             <==> { assert (tree_req (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1)) sl0
                     <==> req (Fl.splitAt_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                              (Fl.apply_pequiv (vequiv_sl p0) sl0))._1)
                 by T.(norm_tree_spec (); smt ()) }
               tree_req (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1)) sl0;
             <==> { U.f_equal tree_req (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1))
                                     (repr_ST_of_M _ c) }
               tree_req (repr_ST_of_M _ c) sl0;
             }

  | TCret #a #x #sl_hint  pre post  p ->
             U.f_equal tree_req (repr_ST_of_M _ (TCret #a #x #sl_hint pre post p))
                                (repr_ST_of_M _ c);
             assert (M.tree_req _ (TCret #a #x #sl_hint pre post p) sl0 == True) by T.(trefl ());
             assert (tree_req (repr_ST_of_M _ (TCret #a #x #sl_hint pre post p)) sl0 <==> True)
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
               introduce forall (x : a) (sl1 : sl_f (itm x)) .
                 (M.tree_ens f cf sl0 x sl1 <==> tree_ens (repr_ST_of_M f cf) sl0 x sl1) /\
                 (M.tree_req (g x) (cg x) sl1 <==> tree_req (repr_ST_of_M (g x) (cg x)) sl1)
               with (repr_ST_of_M_ens f cf sl0 x sl1; repr_ST_of_M_req (g x) (cg x) sl1)
             }
               tree_req (repr_ST_of_M f cf) sl0 /\
               (forall (x : a) (sl1 : Fl.flist (vprop_list_sels_t (itm x))) .
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
              wp (fun x -> tree_req (repr_ST_of_M (g x) (cg x)) sl0);
            <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
              tree_req (repr_ST_of_M _ (TCbindP #a #b #wp #x #g pre post cg)) sl0;
            <==> {U.f_equal tree_req (repr_ST_of_M _ (TCbindP #a #b #wp #x #g pre post cg)) (repr_ST_of_M _ c)}
              tree_req (repr_ST_of_M _ c) sl0;
            }

and repr_ST_of_M_ens (#a : Type) (t : M.prog_tree a)
                     (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
                     (sl0 : sl_f pre) (res : a) (sl1 : sl_f (post res))
  : Lemma (ensures M.tree_ens t c sl0 res sl1 <==> tree_ens (repr_ST_of_M t c) sl0 res sl1)
          (decreases t)
  = match c as c returns squash (M.tree_ens t c sl0 res sl1 <==> tree_ens (repr_ST_of_M t c) sl0 res sl1) with
    | TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1 ->
             L.map_append Mkvprop'?.t pre frame;
             L.map_append Mkvprop'?.t (post res) frame;

             calc (<==>) {
               M.tree_ens _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1) sl0 res sl1;
             <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ()) }
              (let fsl0, frame0 = extract_vars_f pre' pre frame p0 sl0 in
               let fsl1, frame1 = extract_vars_f (post' res) (post res) frame
                                                 (Perm.pequiv_sym (p1 res)) sl1 in
                frame1 == frame0 /\ ens fsl0 res fsl1);
             <==> { }
              (let fsl0, frame0 = Fl.splitAt_ty (vprop_list_sels_t pre) (vprop_list_sels_t frame)
                                                  (Fl.apply_pequiv (vequiv_sl p0) sl0) in
               let fsl1, frame1 = Fl.splitAt_ty (vprop_list_sels_t (post res)) (vprop_list_sels_t frame)
                                                  (Fl.apply_pequiv (Perm.pequiv_sym (vequiv_sl (p1 res))) sl1) in
                frame1 == frame0 /\ ens fsl0 res fsl1);
             <==> {repr_ST_of_M__TCspec_ens req ens pre' post' frame p0 p1 sl0 res sl1}
               tree_ens (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame p0 p1)) sl0 res sl1;
             <==> {U.f_equal tree_ens (repr_ST_of_M _ (TCspec #a #pre #post #req #ens  pre' post' frame  p0 p1))
                                    (repr_ST_of_M _ c)}
               tree_ens (repr_ST_of_M _ c) sl0 res sl1;
             }

  | TCret #a #x #sl_hint  pre post  p ->
             calc (<==>) {
               M.tree_ens _ (TCret #a #x #sl_hint pre post p) sl0 res sl1;
             <==> { assert (M.tree_ens _ (TCret #a #x #sl_hint pre post p) sl0 res sl1 <==>
                           (res == x /\ sl1 == extract_vars p sl0))
                      by T.(norm [delta_only [`%M.tree_ens]; zeta; iota]; smt ()) }
               res == x /\ sl1 == extract_vars p sl0;
             <==> {}
               res == x /\ sl1 == Fl.apply_pequiv (vequiv_sl p) sl0;
             <==> { assert (tree_ens (repr_ST_of_M _ (TCret #a #x #sl_hint pre post p)) sl0 res sl1 <==>
                           (res == x /\ sl1 == Fl.apply_pequiv (vequiv_sl p) sl0))
                      by T.(norm_tree_spec (); smt ()) }
               tree_ens (repr_ST_of_M _ (TCret #a #x #sl_hint pre post p)) sl0 res sl1;
             <==> { U.f_equal tree_ens (repr_ST_of_M _ (TCret #a #x #sl_hint pre post p))
                                    (repr_ST_of_M _ c) }
               tree_ens (repr_ST_of_M _ c) sl0 res sl1;
             }

  | TCbind #a #b #f #g  pre itm post  cf cg ->
             calc (<==>) {
               M.tree_ens _ (TCbind #a #b #f #g  pre itm post  cf cg) sl0 res sl1;
             <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
               bind_ens (M.tree_ens f cf) (fun x -> M.tree_ens (g x) (cg x)) sl0 res sl1;
             <==> {
               introduce forall (x : a) (sl1' : sl_f (itm x)) .
                 (M.tree_ens f cf sl0 x sl1' <==> tree_ens (repr_ST_of_M f cf) sl0 x sl1') /\
                 (M.tree_ens (g x) (cg x) sl1' res sl1 <==> tree_ens (repr_ST_of_M (g x) (cg x)) sl1' res sl1)
               with (repr_ST_of_M_ens f cf sl0 x sl1';
                     repr_ST_of_M_ens (g x) (cg x) sl1' res sl1)
             }
               (exists (x : a) (sl1' : Fl.flist (vprop_list_sels_t (itm x))) .
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
              introduce forall (x : a).
                 (M.tree_ens (g x) (cg x) sl0 res sl1 <==> tree_ens (repr_ST_of_M (g x) (cg x)) sl0 res sl1)
               with repr_ST_of_M_ens (g x) (cg x) sl0 res sl1
            }
              (exists (x : a) . as_ensures wp x /\ tree_ens (repr_ST_of_M (g x) (cg x)) sl0 res sl1);
            <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
              tree_ens (repr_ST_of_M _ (TCbindP #a #b #wp #x #g pre post cg)) sl0 res sl1;
            <==> {U.f_equal tree_ens (repr_ST_of_M _ (TCbindP #a #b #wp #x #g pre post cg))
                                   (repr_ST_of_M _ c)}
              tree_ens (repr_ST_of_M _ c) sl0 res sl1;
            }
#pop-options


(***** Shape *)

let repr_ST_of_M_shape__norm : list norm_step =
  [delta_only [`%prog_has_shape'; `%repr_ST_of_M; `%shape_ST_of_M; `%bind];
   iota; zeta]

#push-options "--ifuel 1"
let rec repr_ST_of_M_shape
      (#a : Type) (t : M.prog_tree a)
      (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
      (#post_n : nat) (s : M.shape_tree (L.length pre) post_n)
   : Lemma (requires M.tree_cond_has_shape c s)
           (ensures  prog_has_shape (repr_ST_of_M t c) (shape_ST_of_M s))
   = match c with
   | TCspec #a #pre #post #req #ens pre1 post1 frame p0 p1 ->
            let M.Sspec pre_n post_n frame_n p0' p1' = s in
            assert (prog_has_shape' (repr_ST_of_M t (TCspec #a #pre #post #req #ens pre1 post1 frame p0 p1))
                                    (shape_ST_of_M (M.Sspec pre_n post_n frame_n p0' p1')))
                by T.(norm repr_ST_of_M_shape__norm; smt ())
  | TCret #a #x #sl_hint  pre post p ->
            let M.Sret n p' = s in
            assert (prog_has_shape' (repr_ST_of_M t (TCret #a #x #sl_hint pre post p))
                                    (shape_ST_of_M (M.Sret n p')))
                by T.(norm repr_ST_of_M_shape__norm; smt ())
  | TCbind #a #b #f #g _ _ _ cf cg ->
            let M.Sbind _ _ _ s_f s_g = s in
            repr_ST_of_M_shape f cf s_f;
            introduce forall (x : a) . prog_has_shape (repr_ST_of_M (g x) (cg x)) (shape_ST_of_M s_g)
              with repr_ST_of_M_shape (g x) (cg x) s_g
  | TCbindP #a #b #_ #_ #g _ _ cg ->
            let M.SbindP _ _ s_g = s in
            introduce forall (x : a) . prog_has_shape (repr_ST_of_M (g x) (cg x)) (shape_ST_of_M s_g)
              with repr_ST_of_M_shape (g x) (cg x) s_g
#pop-options


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
  | TbindP a b pre post wp f g ->
             let t = TbindP a b pre post wp f g in
             let g1 (x : a) = flatten_prog (g x) in
             assert (flatten_prog_aux t k == k (TbindP _ _ _ _ wp f g1))
               by T.(trefl ());
             equiv_TbindP wp f g1 g
               (fun x -> flatten_equiv (g x));
             k_equiv _ (TbindP _ _ _ _ wp f g1) t

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
  | TbindP a b pre post wp f g ->
           let t = TbindP a b pre post wp f g in
           let SbindP _ _ s_g = s in
           let g1 (x : a) = flatten_prog (g x) in
           assert (flatten_prog_aux t k_t == k_t (TbindP _ _ _ _ wp f g1))
             by T.(trefl ());
           introduce forall (x : a) . prog_has_shape (g1 x) (flatten_shape s_g)
             with flatten_prog_shape (g x) s_g;
           k_hyp _ (TbindP _ _ _ _ wp f g1) (SbindP _ _ (flatten_shape s_g))

#pop-options
