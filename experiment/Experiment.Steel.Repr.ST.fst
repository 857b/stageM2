module Experiment.Steel.Repr.ST

module L = FStar.List.Pure
module T = FStar.Tactics
module TLogic = Learn.Tactics.Logic
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

(**** soundness of M --> ST *)

(***** Spec *)

let norm_M2ST () : T.Tac unit
  = T.norm [delta_only [`%repr_ST_of_M; `%repr_ST_of_M_Spec; `%post_ST_of_M; `%bind;
                        `%tree_req; `%tree_ens; `%const_post; `%frame_post;
                        `%M.tree_req; `%M.tree_ens; `%M.spec_req; `%M.spec_ens;
                        `%Mksequiv?.seq_req; `%Mksequiv?.seq_ens; `%Mksequiv?.seq_eq;
                        `%Mktuple2?._1; `%Mktuple2?._2;
                        `%return_req; `%return_ens];
            delta_attr [`%U.__util_func__];
            delta_qualifier ["unfold"];
            zeta; iota; simplify]


let rew_forall_flist_app (t0 t1 : Fl.ty_list) (p0 : Fl.flist L.(t0 @ t1) -> Type) (p1 : Type)
    (_ : squash ((forall (x0 : Fl.flist t0) (x1 : Fl.flist t1) . p0 (Fl.append x0 x1)) <==> p1))
  : squash ((forall (x : Fl.flist L.(t0 @ t1)) . p0 x) <==> p1)
  = FStar.Classical.forall_intro (Fl.splitAt_ty_append t0 t1)

let rew_exists_flist_app (t0 t1 : Fl.ty_list) (p0 : Fl.flist L.(t0 @ t1) -> Type) (p1 : Type)
    (_ : squash ((exists (x0 : Fl.flist t0) (x1 : Fl.flist t1) . p0 (Fl.append x0 x1)) <==> p1))
  : squash ((exists (x : Fl.flist L.(t0 @ t1)) . p0 x) <==> p1)
  = FStar.Classical.forall_intro (Fl.splitAt_ty_append t0 t1)

let rew_append_inj (t0 t1 : Fl.ty_list) (x0 x1 : Fl.flist t0) (y0 y1 : Fl.flist t1)
  : squash ((eq2 (Fl.append x0 y0) (Fl.append x1 y1)) <==> (x0 == x1 /\ y0 == y1))
  = Fl.append_splitAt_ty _ _ x0 y0; Fl.append_splitAt_ty _ _ x1 y1

let rew_append_inj' #eq_t (t0 t1 : Fl.ty_list) (x0 x1 : Fl.flist t0) (y0 y1 : Fl.flist t1)
    (_ : squash (eq_t == Fl.flist L.(t0 @ t1)))
  : squash ((eq2 #eq_t (Fl.append x0 y0) (Fl.append x1 y1)) <==> (x0 == x1 /\ y0 == y1))
  = Fl.append_splitAt_ty _ _ x0 y0; Fl.append_splitAt_ty _ _ x1 y1

let rew_seq_of_vequiv_ens1 #pre #post (eqv : vequiv pre post) sl0 sl1
  : squash (seq_ens1 #(vprop_list_sels_t pre) #(vprop_list_sels_t post)
                     (sequiv_of_vequiv #pre #post eqv) sl0 sl1
            <==> veq_ens1 eqv sl0 sl1)
  = ()

let stop_veq_ens1 #pre #post (eqv : vequiv pre post) sl0 sl1
  : squash (veq_ens1 eqv sl0 sl1 <==> veq_ens1 eqv sl0 sl1)
  = ()

let rew_iff_M2ST () : Tac unit =
  TLogic.rew_iff (fun r -> first [
    (fun () -> apply (`rew_seq_of_vequiv_ens1));
    (fun () -> apply (`stop_veq_ens1));
    (fun () -> apply (`rew_append_inj));
    (fun () -> apply (`rew_forall_flist_app); r ());
    (fun () -> apply (`rew_exists_flist_app); r ())
  ])

let rew_vprop_list_sels_t_app (v0 v1 : M.vprop_list)
  : Lemma (vprop_list_sels_t L.(v0 @ v1) == L.(vprop_list_sels_t v0 @ vprop_list_sels_t v1))
  = L.map_append Mkvprop'?.t v0 v1

let simplify_repr_ST_of_M_Spec () : Tac unit
  =
    let rew_iff () = apply (`TLogic.rew_iff_right); rew_iff_M2ST (); norm [] in
    norm_M2ST ();
    rew_iff ();
    l_to_r [(`rew_vprop_list_sels_t_app)];
    rew_iff ();
    norm [delta_only [`%sequiv_of_vequiv]];
    l_to_r [(`Fl.append_splitAt_ty)];
    norm_M2ST ();
    rew_iff ()

#push-options "--ifuel 0"
let repr_ST_of_M_req__Spec #a #pre #post req ens (tcs : tree_cond_Spec a pre post)
                           (sl0 : sl_f tcs.tcs_pre)
  : Lemma (M.spec_req tcs req ens sl0 <==> tree_req (repr_ST_of_M_Spec a pre post req ens tcs) sl0)
  =
    L.map_append Mkvprop'?.t pre tcs.tcs_frame;

    assert (M.spec_req tcs req ens sl0 <==> tree_req (repr_ST_of_M_Spec a pre post req ens tcs) sl0)
      by (
        simplify_repr_ST_of_M_Spec ();
        // smt () works directly
        TLogic.(
        apply (`conj_morph_iff);
          apply (`iff_refl);
        apply (`forall_morph_iff); let sl0' = intro () in
        apply (`forall_morph_iff); let sl_frame = intro () in
        apply (`impl_morph_iff);
          apply (`conj_morph_iff); apply (`iff_refl); smt ();
        apply (`conj_morph_iff); apply (`iff_refl);
        apply (`forall_morph_iff); let x = intro () in
        apply (`forall_morph_iff); let sl1' = intro () in
        smt ())
      )

let repr_ST_of_M_ens__Spec #a #pre #post req ens (tcs : tree_cond_Spec a pre post)
                           (sl0 : sl_f tcs.tcs_pre) (x : a) (sl1 : sl_f (tcs.tcs_post x))
  : Lemma (M.spec_ens tcs ens sl0 x sl1 <==> tree_ens (repr_ST_of_M_Spec a pre post req ens tcs) sl0 x sl1)
  =
    L.map_append Mkvprop'?.t pre tcs.tcs_frame;
    L.map_append Mkvprop'?.t (post x) tcs.tcs_frame;
    assert (M.spec_ens tcs ens sl0 x sl1 <==> tree_ens (repr_ST_of_M_Spec a pre post req ens tcs) sl0 x sl1)
      by (simplify_repr_ST_of_M_Spec (); smt ())
#pop-options

#push-options "--z3rlimit 30 --ifuel 1"
let rec repr_ST_of_M_req (#a : Type) (t : M.prog_tree a)
                         (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
                         (sl0 : sl_f pre)
  : Lemma (ensures M.tree_req t c sl0 <==> tree_req (repr_ST_of_M t c) sl0)
          (decreases t)
  = match c as c returns squash (M.tree_req t c sl0 <==> tree_req (repr_ST_of_M t c) sl0) with
  | TCspec #a #pre #post #req #ens  tcs ->
             repr_ST_of_M_req__Spec req ens tcs sl0

  | TCspecS #a #pre #post #req #ens  tr tcs ->
             repr_ST_of_M_req__Spec tr.r_req tr.r_ens tcs sl0

  | TCret #a #x #sl_hint  pre post  e ->
             let c = TCret #a #x #sl_hint pre post e in
             assert (M.tree_req _ c sl0 <==> tree_req (repr_ST_of_M _ c) sl0)
               by (norm_M2ST (); norm [delta_only [`%sequiv_of_vequiv]]; norm_M2ST (); smt ())

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

  | TCbindP #a #b #wp #g  pre post  cg ->
            calc (<==>) {
              M.tree_req _ c sl0;
            <==> {}
              M.tree_req _ (TCbindP #a #b #wp #g pre post cg) sl0;
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
              tree_req (repr_ST_of_M _ (TCbindP #a #b #wp #g pre post cg)) sl0;
            <==> {U.f_equal tree_req (repr_ST_of_M _ (TCbindP #a #b #wp #g pre post cg)) (repr_ST_of_M _ c)}
              tree_req (repr_ST_of_M _ c) sl0;
            }
  | TCif #a #guard #thn #els  pre post  cthn cels ->
            if guard
            then repr_ST_of_M_req thn cthn sl0
            else repr_ST_of_M_req els cels sl0
  

and repr_ST_of_M_ens (#a : Type) (t : M.prog_tree a)
                     (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
                     (sl0 : sl_f pre) (res : a) (sl1 : sl_f (post res))
  : Lemma (ensures M.tree_ens t c sl0 res sl1 <==> tree_ens (repr_ST_of_M t c) sl0 res sl1)
          (decreases t)
  = match c as c returns squash (M.tree_ens t c sl0 res sl1 <==> tree_ens (repr_ST_of_M t c) sl0 res sl1) with
    | TCspec #a #pre #post #req #ens  tcs ->
             repr_ST_of_M_ens__Spec req ens tcs sl0 res sl1

  | TCspecS #a #pre #post #req #ens  tr tcs ->
             repr_ST_of_M_ens__Spec tr.r_req tr.r_ens tcs sl0 res sl1

  | TCret #a #x #sl_hint  pre post  e ->
             let c = TCret #a #x #sl_hint pre post e in
             assert (M.tree_ens _ c sl0 res sl1 <==> tree_ens (repr_ST_of_M _ c) sl0 res sl1)
               by (norm_M2ST (); apply (`TLogic.rew_iff_right); rew_iff_M2ST (); norm []; smt ())

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

  | TCbindP #a #b #wp #g  pre post  cg ->
            calc (<==>) {
              M.tree_ens _ c sl0 res sl1;
            <==> {}
              M.tree_ens _ (TCbindP #a #b #wp #g pre post cg) sl0 res sl1;
            <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
              bind_pure_ens wp (fun x -> M.tree_ens (g x) (cg x)) sl0 res sl1;
            <==> {
              introduce forall (x : a).
                 (M.tree_ens (g x) (cg x) sl0 res sl1 <==> tree_ens (repr_ST_of_M (g x) (cg x)) sl0 res sl1)
               with repr_ST_of_M_ens (g x) (cg x) sl0 res sl1
            }
              (exists (x : a) . as_ensures wp x /\ tree_ens (repr_ST_of_M (g x) (cg x)) sl0 res sl1);
            <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
              tree_ens (repr_ST_of_M _ (TCbindP #a #b #wp #g pre post cg)) sl0 res sl1;
            <==> {U.f_equal tree_ens (repr_ST_of_M _ (TCbindP #a #b #wp #g pre post cg))
                                   (repr_ST_of_M _ c)}
              tree_ens (repr_ST_of_M _ c) sl0 res sl1;
            }

  | TCif #a #guard #thn #els  pre post  cthn cels ->
            if guard
            then repr_ST_of_M_ens thn cthn sl0 res sl1
            else repr_ST_of_M_ens els cels sl0 res sl1
#pop-options


(***** Shape *)

let repr_ST_of_M_shape__norm : list norm_step =
  [delta_only [`%prog_has_shape'; `%repr_ST_of_M; `%repr_ST_of_M_Spec; `%shape_ST_of_M; `%bind];
   delta_qualifier ["unfold"];
   iota; zeta]

#push-options "--ifuel 1"
let rec repr_ST_of_M_shape
      (#a : Type) (t : M.prog_tree a)
      (#pre : M.pre_t) (#post : M.post_t a) (c : M.tree_cond t pre post)
      (#post_n : nat) (s : M.shape_tree (L.length pre) post_n)
   : Lemma (requires M.tree_cond_has_shape c s)
           (ensures  prog_has_shape (repr_ST_of_M t c) (shape_ST_of_M s))
   = match c with
   | TCspec #a #pre #post #req #ens tcs ->
            let M.Sspec pre_n post_n pre'_n post'_n frame_n e0' e1' = s in
            assert (prog_has_shape' (repr_ST_of_M t (TCspec #a #pre #post #req #ens tcs))
                                    (shape_ST_of_M (M.Sspec pre_n post_n pre'_n post'_n frame_n e0' e1')))
                by T.(norm repr_ST_of_M_shape__norm; smt ())
   | TCspecS #a #pre #post #req #ens tr tcs ->
            let M.Sspec pre_n post_n pre'_n post'_n frame_n e0' e1' = s in
            assert (prog_has_shape' (repr_ST_of_M t (TCspecS #a #pre #post #req #ens tr tcs))
                                    (shape_ST_of_M (M.Sspec pre_n post_n pre'_n post'_n frame_n e0' e1')))
                by T.(norm repr_ST_of_M_shape__norm; smt ())
   | TCret #a #x #sl_hint  pre post p ->
            let M.Sret pre_n post_n e' = s in
            assert (prog_has_shape' (repr_ST_of_M t (TCret #a #x #sl_hint pre post p))
                                    (shape_ST_of_M (M.Sret pre_n post_n e')))
                by T.(norm repr_ST_of_M_shape__norm; smt ())
   | TCbind #a #b #f #g _ _ _ cf cg ->
            let M.Sbind _ _ _ s_f s_g = s in
            repr_ST_of_M_shape f cf s_f;
            introduce forall (x : a) . prog_has_shape (repr_ST_of_M (g x) (cg x)) (shape_ST_of_M s_g)
              with repr_ST_of_M_shape (g x) (cg x) s_g
   | TCbindP #a #b #_ #g _ _ cg ->
            let M.SbindP _ _ s_g = s in
            introduce forall (x : a) . prog_has_shape (repr_ST_of_M (g x) (cg x)) (shape_ST_of_M s_g)
              with repr_ST_of_M_shape (g x) (cg x) s_g
  | TCif #a #guard #thn #els  pre post  cthn cels ->
            let M.Sif _ _ s_thn s_els = s in
            repr_ST_of_M_shape thn cthn s_thn;
            repr_ST_of_M_shape els cels s_els
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
