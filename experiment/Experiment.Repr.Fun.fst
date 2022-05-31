module Experiment.Repr.Fun

module T = FStar.Tactics
open FStar.Classical.Sugar
open FStar.Calc


(***** Equivalence *)

#push-options "--ifuel 0 --fuel 1"
let equiv_Tbind
      (#s : tys) (#a #b : s.t)
      (f f' : prog_tree a) (g g' : (x : s.v a) -> prog_tree b)
      (eq_f : squash (equiv f f')) (eq_g : (x : s.v a) -> squash (equiv (g x) (g' x)))
  : Lemma (equiv (Tbind a b f g) (Tbind a b f' g'))
  = 
    FStar.Classical.forall_intro_squash_gtot eq_g;
    assert (equiv (Tbind a b f g) (Tbind a b f' g'))
      by T.(//unfold one level of tree_ens / tree_req
            norm [delta_only [`%equiv; `%tree_req; `%tree_ens]; zeta];
            norm [iota];
            smt ())

let equiv_TbindP
      (#s : tys) (#a : Type) (#b : s.t) (wp : pure_wp a)
      (g g' : (x : a) -> prog_tree b)
      (eq_g : (x : a) -> squash (equiv (g x) (g' x)))
  : Lemma (equiv (TbindP a b wp g) (TbindP a b wp g'))
  =
    FStar.Classical.forall_intro_squash_gtot eq_g;
    MP.elim_pure_wp_monotonicity wp;
    assert (equiv (TbindP a b wp g) (TbindP a b wp g'))
      by T.(norm [delta_only [`%equiv; `%tree_req; `%tree_ens]; zeta];
            norm [iota];
            smt ())

let equiv_Tif
      (#s : tys) (#a : s.t) (guard : bool)
      (thn thn' : prog_tree a) (els els' : prog_tree a)
      (eq_thn : squash (equiv thn thn')) (eq_els : squash (equiv els els'))
  : Lemma (equiv (Tif a guard thn els) (Tif a guard thn' els'))
  =
    assert (equiv (Tif a guard thn els) (Tif a guard thn' els'))
      by T.(norm [delta_only [`%equiv; `%tree_req; `%tree_ens]; zeta];
            norm [iota];
            smt ())


let equiv_Tbind_assoc_Tbind
      (#s : tys) (#a #b #c : s.t)
      (f : prog_tree #s a) (g : (x : s.v a) -> prog_tree b) (h : (y : s.v b) -> prog_tree c)
  : Lemma (equiv (bind (bind f g) h) (bind f (fun x -> bind (g x) h)))
  =
    assert (equiv (bind (bind f g) h) (bind f (fun x -> bind (g x) h)))
      by T.(norm [delta_only [`%equiv; `%tree_req; `%tree_ens; `%bind]; zeta];
            norm [iota];
            smt ())
#pop-options

(**) let __end_section_equiv = ()

(***** Weakest-precondition *)

let rec tree_wp_sound (#s : tys) (#a : s.t) (t : prog_tree #s a) (post : pure_post (s.v a))
  : Lemma (requires tree_wp t post)
          (ensures  tree_req t /\ (forall (x : s.v a) . tree_ens t x ==> post x))
          (decreases t)
  = match t with
  | Tnew _ | Tasrt _ | Tasum _ | Tret _ _ | Tspec _ _ _ -> ()
  | Tbind a b f g ->
      let post1 (x : s.v a) = tree_wp (g x) post in
      assert (tree_wp (Tbind a b f g) post == tree_wp f post1) by T.(trefl ());
      tree_wp_sound f post1;
      introduce forall (x : s.v a) . tree_wp (g x) post ==> (tree_req (g x) /\ (forall (y : s.v b) . tree_ens (g x) y ==> post y))
        with introduce _ ==> _ with _ . tree_wp_sound (g x) post
  | TbindP a b wp g ->
      let post1 (x : a) = tree_wp (g x) post in
      let req1  (x : a) = tree_req (g x)     in
      assert (tree_wp (TbindP a b wp g) post == wp post1) by T.(trefl ());
      MP.elim_pure_wp_monotonicity wp;
      introduce forall (x : a) . post1 x ==> (req1 x /\ (forall (y : s.v b) . tree_ens (g x) y ==> post y))
        with introduce _ ==> _ with _ . tree_wp_sound (g x) post;
      assert (tree_req (TbindP a b wp g) == wp req1) by T.(trefl ());
      U.prop_equal (fun p -> p) (wp req1) (tree_req (TbindP a b wp g))
  | Tif a guard thn els ->
      if guard
      then tree_wp_sound thn post
      else tree_wp_sound els post


(*** Returns elimination *)

unfold
let equiv_with_fun (#st : tys) (#a #b : st.t) (f : prog_tree #st a) (g : prog_tree #st b) (h : st.v a -> st.v b)
  : prop
  = (tree_req g <==> tree_req f) /\
    (forall (y : st.v b) . tree_req f ==>
       (tree_ens g y <==> (exists (x : st.v a) . tree_ens f x /\ y == h x)))

let equiv_bind_ret (#st : tys) (#a #b : st.t) (f : prog_tree #st a) (g : st.v a -> st.v b) (f' : prog_tree #st b)
  : Lemma (requires equiv (Tbind _ _ f (elim_returns_k_ret g)) f')
          (ensures  equiv_with_fun f f' g)
  = ()

let fseq (#a #b #c : Type) (f : a -> b) (g : b -> c) (x : a) = g (f x)

let equiv_ret_ret (#st : tys) (#a #b #c : st.t) (f : st.v a -> st.v b) (g : st.v b -> st.v c) (x : st.v a)
  : Lemma (equiv (Tbind _ _ (elim_returns_k_ret f x) (elim_returns_k_ret g))
                 (elim_returns_k_ret (fseq f g) x))
  = ()

#push-options "--ifuel 0"
let equiv_bind_ret_ret (#st : tys) (#a #b #c : st.t) (f : prog_tree #st a)
                       (g : st.v a -> st.v b) (h : st.v b -> st.v c)
  : Lemma (equiv (Tbind _ _ (Tbind _ _ f (elim_returns_k_ret g)) (elim_returns_k_ret h))
                 (Tbind _ _ f (elim_returns_k_ret (fseq g h))))
  =
    let gh (x : st.v a) = Tbind _ _ (elim_returns_k_ret g x) (elim_returns_k_ret h) in 
    calc (equiv) {
      Tbind _ _ (Tbind _ _ f (elim_returns_k_ret g)) (elim_returns_k_ret h);
    equiv { equiv_Tbind_assoc_Tbind f (elim_returns_k_ret g) (elim_returns_k_ret h) }
      Tbind _ _ f gh;
    equiv { equiv_Tbind f f gh (elim_returns_k_ret (fseq g h)) () (equiv_ret_ret g h) }
      Tbind _ _ f (elim_returns_k_ret (fseq g h));
    }
#pop-options

#push-options "--ifuel 1 --z3rlimit 30"
let rec elim_returns_equiv
      (#st : tys) (lm : tys_lam st) (#a : st.t) (t : prog_tree #st a) (s : prog_shape t)
  : Lemma (ensures equiv (elim_returns lm t s) t) (decreases %[t; 1])
  =
    let id (x : st.v a) = x in
    assert (elim_returns lm t s == elim_returns_aux lm t s (ERetKfun id)) by T.(trefl ());
    elim_returns_equiv_aux lm t s (ERetKfun id)

and elim_returns_equiv_aux
      (#st : tys) (lm : tys_lam st) (#a : st.t) (t : prog_tree #st a) (s : prog_shape t)
      (#a1 : st.t) (k : elim_returns_k st a a1)
  : Lemma (ensures equiv (elim_returns_aux lm t s k) (Tbind a a1 t (elim_returns_k_trm k)))
          (decreases %[t; 0])
  =
  let bind (#a : st.t) (#b : st.t) (f : prog_tree #st a) (g : st.v a -> prog_tree #st b) : prog_tree #st b
    = Tbind a b f (lm.lam_tree g)
  in
  match t with
  | Tnew _ | Tasrt _ | Tasum _ | Tspec _ _ _ -> ()
  | Tret _ _ -> ()

  | Tbind a b f g ->
           let t = Tbind a b f g in
           let Sbind s_f s_g = s in
           let s = Sbind s_f s_g in
           let k1_f (_ : squash (Sret? s_g)) (kf : st.v b -> st.v a1) (x : st.v a) =
             kf (st.v_of_r (Tret?.x (g x)))                       in
           let k1_t (x : st.v a) = elim_returns_aux lm (g x) s_g k   in
           assert (elim_returns_aux lm t s k == (
             match s_g, k with
              | Sret true, ERetKfun kf -> elim_returns_aux lm f s_f (ERetKfun (k1_f () kf))
              | _ -> elim_returns_aux lm f s_f (ERetKtrm k1_t)
             )) by T.(trefl ());

           begin match s_g, k with
           | Sret true, ERetKfun kf ->
              let k1_f = k1_f () kf                           in
              let gf (x : st.v a) = st.v_of_r (Tret?.x (g x)) in
              calc (equiv) {
                elim_returns_aux lm t s k;
              == { assert (elim_returns_aux lm t (Sbind s_f (Sret true)) (ERetKfun kf)
                         == elim_returns_aux lm f s_f (ERetKfun k1_f))
                      by T.(trefl ()) }
                elim_returns_aux lm f s_f (ERetKfun k1_f);
              equiv { elim_returns_equiv_aux lm f s_f (ERetKfun k1_f) }
                Tbind _ _ f (elim_returns_k_ret k1_f);
              == { assert (Tbind _ _ f (elim_returns_k_ret k1_f)
                        == Tbind _ _ f (elim_returns_k_ret (fseq gf kf)))
                     by T.(trefl ()) }
                Tbind _ _ f (elim_returns_k_ret (fseq gf kf));
              equiv { equiv_bind_ret_ret f gf kf }
                Tbind _ _ (Tbind _ _ f (elim_returns_k_ret gf)) (elim_returns_k_ret kf);
              equiv { equiv_Tbind f f (elim_returns_k_ret gf) g () (fun x -> ());
                      equiv_Tbind (Tbind _ _ f (elim_returns_k_ret gf)) t
                                  (elim_returns_k_ret kf) (elim_returns_k_ret kf)
                                  () (fun x -> ()) }
                Tbind _ _ t (elim_returns_k_trm k);
              }
           | _ ->
              let k2 (x : st.v a) = Tbind _ _ (g x) (elim_returns_k_trm k) in
              calc (equiv) {
                elim_returns_aux lm t s k;
              == { }
                elim_returns_aux lm f s_f (ERetKtrm k1_t);
              equiv { elim_returns_equiv_aux lm f s_f (ERetKtrm k1_t) }
                Tbind _ _ f k1_t;
              equiv { equiv_Tbind f f k1_t k2 () (fun x -> elim_returns_equiv_aux lm (g x) s_g k) }
                Tbind _ _ f k2;
              equiv { equiv_Tbind_assoc_Tbind f g (elim_returns_k_trm k) }
                Tbind _ _ t (elim_returns_k_trm k);
              }
           end

  | TbindP a b wp g ->
           let t = TbindP a b wp g in
           let SbindP s_g = s      in
           let s = SbindP s_g      in
           begin match k with
           | ERetKfun kf ->
              let g1 (x : a) = elim_returns_aux lm (g x) s_g (ERetKfun #st #b kf) in
              assert (elim_returns_aux lm t s (ERetKfun kf) == TbindP _ _ wp g1)
                by T.(trefl ());
              introduce forall (x : a) . equiv_with_fun (g x) (g1 x) kf
                with (elim_returns_equiv_aux lm (g x) s_g (ERetKfun #st #b kf);
                      equiv_bind_ret (g x) kf (g1 x));
              MP.elim_pure_wp_monotonicity wp
           | ERetKtrm kt ->
               let g1 (x : a) = elim_returns lm (g x) s_g in
               assert (elim_returns_aux lm t s (ERetKtrm kt) == bind (TbindP _ _ wp g1) kt)
                 by T.(trefl ());
               equiv_TbindP wp g1 g (fun x -> elim_returns_equiv lm (g x) s_g);
               equiv_Tbind (TbindP _ _ wp g1) (TbindP _ _ wp g) kt kt () (fun _ -> ())
           end

  | Tif a guard thn els ->
           let Sif s_thn s_els = s in
           equiv_Tbind
             (Tif a guard (elim_returns lm thn s_thn) (elim_returns lm els s_els)) (Tif a guard thn els)
             (elim_returns_k_trm k) (elim_returns_k_trm k)
             (equiv_Tif guard (elim_returns lm thn s_thn) thn (elim_returns lm els s_els) els
                        (elim_returns_equiv lm thn s_thn) (elim_returns_equiv lm els s_els))
             (fun _ -> ())
#pop-options
