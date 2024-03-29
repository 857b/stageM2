module Experiment.Steel.Repr.ST_to_SF.Spec

module T = FStar.Tactics
open FStar.Calc
open Learn.Logic

#set-options "--fuel 1 --ifuel 1"


let rec post_src_of_shape_ty
      (#a : Type) (#pre0 : ST.pre_t) (#post0 : ST.post_t a) (t : ST.prog_tree a pre0 post0)
      (s : ST.prog_shape t) (x : a) (i : Fin.fin (L.length (post0 x)) {Some? (post_src_f_of_shape s.shp i)})
  : Lemma (ensures  L.index (post0 x) i == L.index pre0 (Some?.v (post_src_f_of_shape s.shp i)))
          (decreases t)
  = match t with
    | ST.Tequiv pre post0 e ->
             let ST.Sequiv pre_n post_n e' = s.shp in
             e.seq_typ
    | ST.Tframe a pre post frame f ->
             let ST.Sframe _ post_n _ s_f = s.shp in
             Ll.append_index (post x) frame i;
             if i < post_n
             then begin
               let Some j = post_src_f_of_shape s_f i in
               Ll.append_index pre frame j;
               post_src_of_shape_ty f (ST.mk_prog_shape f s_f) x i
             end else Ll.append_index pre frame (i - post_n + L.length pre)
    | ST.Tspec  _ pre post _ _ -> ()
    | ST.Tret _ _ _ | ST.Tbind _ _  _ _ _  _ _ | ST.TbindP _ _  _ _  _ _ -> ()
    | ST.Tif _ _ pre post thn els ->
             let ST.Sif _ post_n shp_thn _ = s.shp in
             post_src_of_shape_ty thn (ST.mk_prog_shape thn shp_thn) x i

#push-options "--z3rlimit 20"
let sell_SF_ST_SF
      (#pre #post : Fl.ty_list)
      (s : post_src pre post) (bij : post_bij_t s)
      (sl0 : Fl.flist pre) (sl1_SF : Fl.flist (postl_SF_of_ST post bij))
  : Lemma (sell_SF_of_ST post bij (sell_ST_of_SF s bij sl0 sl1_SF) == sl1_SF)
  = Fl.flist_extensionality
         (sell_SF_of_ST post bij (sell_ST_of_SF s bij sl0 sl1_SF)) sl1_SF
    begin fun i ->
      let sl1_ST = sell_ST_of_SF s bij sl0 sl1_SF in
      calc (==) {
        sell_SF_of_ST post bij sl1_ST i;
      == {_ by T.(trefl ())}
        U.cast (L.index (postl_SF_of_ST post bij) i)
          (sl1_ST (bij.idx_ST i));
      == {}
        sl1_SF (bij.idx_SF (bij.idx_ST i));
      == {}
        sl1_SF i;
      }
   end
#pop-options


let post_SF_of_ST__frame
      (#a : Type) (post : ST.post_t a) (frame: Fl.ty_list)
      (pre_n : nat) (post_n : nat {post_has_len post post_n}) (f : ST.shape_tree pre_n post_n)
  : Lemma (post_SF_of_ST (ST.frame_post post frame) (Sframe pre_n post_n (L.length frame) f)
                == post_SF_of_ST post f)
  = 
    let post0 = post_SF_of_ST (ST.frame_post post frame) (Sframe pre_n post_n (L.length frame) f) in
    let post1 = post_SF_of_ST post f in
    U.funext_eta post0 post1
         (assert (post0 == U.eta post0) by T.(trefl ()))
         (assert (post1 == U.eta post1) by T.(trefl ()))
         (fun x -> Ll.list_extensionality (post0 x) (post1 x)
           (fun i -> Ll.append_index (post x) frame ((post_bij f).idx_ST i)))

// TODO: factorize
let post_SF_of_ST__spec #a post pre_n post_n
  =
    let post' = post_SF_of_ST post (ST.Sspec pre_n post_n) in
    U.funext_eta post' (U.eta post)
         (assert (post' == U.eta post') by T.(trefl ())) (_ by T.(trefl ()))
         (fun x -> Ll.list_extensionality (post' x) (post x) (fun i -> ()))

let post_SF_of_ST__ret #a post smp_ret post_n
  =
    let post' = post_SF_of_ST post (ST.Sret smp_ret post_n) in
    U.funext_eta post' (U.eta post)
         (assert (post' == U.eta post') by T.(trefl ())) (_ by T.(trefl ()))
         (fun x -> Ll.list_extensionality (post' x) (post x) (fun i -> ()))


(*** Soundness *)

#push-options "--fuel 1 --ifuel 0"

let sell_ST_of_SF_eq_src #pre #post s bij sl0 sl1_SF = ()

#push-options "--z3rlimit 10"
let post_eq_src_ST_SF_ST
      (#pre #post : Fl.ty_list)
      (s : post_src pre post) (bij : post_bij_t s)
      (sl0 : Fl.flist pre) (sl1_ST : Fl.flist post)
  : Lemma (requires post_eq_src s sl0 sl1_ST)
          (ensures  sell_ST_of_SF s bij sl0 (sell_SF_of_ST post bij sl1_ST) == sl1_ST)
  =
    Fl.flist_extensionality (sell_ST_of_SF s bij sl0 (sell_SF_of_ST post bij sl1_ST)) sl1_ST
    begin fun i ->
      match s i with
      | Some j -> calc (==) {
                   sell_ST_of_SF s bij sl0 (sell_SF_of_ST post bij sl1_ST) i;
                 == {}
                   U.cast (L.index post i) (sl0 j);
                 == {(* by [post_eq_src] *)}
                   sl1_ST i;
                 }
      | None -> ()
    end
#pop-options


let normal_equiv : list norm_step = [
  delta_only [`%req_equiv; `%ens_equiv; `%repr_SF_of_ST; `%return_SF_post_of_ST;
              `%ST.tree_req; `%ST.tree_ens; `%tree_req; `%tree_ens;
              `%ST.Mkprog_shape?.shp; `%ST.Mkprog_shape?.post_len; `%ST.mk_prog_shape];
  iota; zeta
]


let repr_SF_of_ST_ens__Tequiv pre post e sl0 sl1
  : Lemma (ens_equiv (ST.Tequiv pre post e)
                      (ST.mk_prog_shape _ (ST.Sequiv _ (L.length post) e.seq_eq)) sl0 U.Unit' sl1)
  =
    let t = ST.Tequiv pre post e                                      in
    let s = ST.mk_prog_shape _ (ST.Sequiv _ (L.length post) e.seq_eq) in
    e.seq_typ;
    let bij = post_bij s.shp               in
    let src : post_src pre post = e.seq_eq in

    FStar.Classical.move_requires (post_eq_src_ST_SF_ST src bij sl0) sl1;
    assert (ens_equiv t s sl0 U.Unit' sl1 <==> (
      seq_ens1 e sl0 sl1 <==> (post_eq_src src sl0 sl1 /\ e.seq_ens sl0 sl1)
    )) by T.(norm normal_equiv;
             norm [delta_only [`%sel_ST_of_SF; `%sel_SF_of_ST; `%post_src_of_shape; `%post_src_f_of_shape;
                               `%ST.Mkprog_shape?.shp; `%const_post];
                   iota; zeta];
             smt ())


#push-options "--z3rlimit 20"
let repr_SF_of_ST_ens__Tframe a pre post frame f
      (post_n : nat {ST.post_has_len post post_n})
      (shp_f : ST.shape_tree _ post_n {ST.prog_has_shape f shp_f})
      sl0 x sl1
      (ens_eq_f : (sl0' : Fl.flist pre) -> (sl1' : Fl.flist (post x)) ->
                  Lemma (ens_equiv f (ST.mk_prog_shape f shp_f) sl0' x sl1'))
  : Lemma (ensures ens_equiv (ST.Tframe a pre post frame f)
                             (ST.mk_prog_shape _ (ST.Sframe _ _ (L.length frame) shp_f)) sl0 x sl1)
  =
    post_SF_of_ST__frame post frame (L.length pre) post_n shp_f;
 
    let t = ST.Tframe a pre post frame f                                                in
    let s = ST.mk_prog_shape t (ST.Sframe (L.length pre) post_n (L.length frame) shp_f) in
    let s_f = ST.mk_prog_shape f shp_f                                                  in
    let post_SF  = sel_SF_of_ST (ST.frame_post post frame) s.shp x sl1                  in
    let post_src_t = post_src_of_shape t s x                                            in

    let sl0', sl_frame0 = Fl.splitAt_ty pre frame sl0    in
    let sl1', sl_frame1 = Fl.splitAt_ty (post x) frame sl1 in
    let rew_split_sl0 () : Lemma (Fl.splitAt_ty pre frame sl0 == (sl0', sl_frame0)) = () in

    assert (ens_equiv t s sl0 x sl1 == (
     (exists (sl1' : Fl.flist (post x)) .
      ST.tree_ens f sl0' x sl1' /\ sl1 == Fl.append sl1' sl_frame0)
    <==>
      (post_eq_src post_src_t sl0 sl1 /\
       tree_ens #_ #(post_SF_of_ST (frame_post post frame) s.shp)
                (repr_SF_of_ST f s_f (Fl.splitAt_ty pre frame sl0)._1) x post_SF)
    )) by T.(norm normal_equiv;
             l_to_r [(``@rew_split_sl0)];
             norm [delta_only [`%Mktuple2?._1]; iota];
             trefl ());

    let post_SF' = sel_SF_of_ST post shp_f x sl1' in
    let post_src_f = post_src_of_shape f s_f x    in
    let bij = post_bij shp_f                      in
  
    U.assert_by ((exists (sl1' : Fl.flist (post x)) . ST.tree_ens f sl0' x sl1' /\ sl1 == Fl.append sl1' sl_frame0)
         <==> (ST.tree_ens f sl0' x sl1' /\ sl_frame1 == sl_frame0))
      (fun () -> Fl.splitAt_ty_append (post x) frame sl1;
              FStar.Classical.forall_intro_2 (Fl.append_splitAt_ty (post x) frame));
    U.assert_by (tree_ens #_ #(post_SF_of_ST (frame_post post frame) s.shp)
                (repr_SF_of_ST f s_f (Fl.splitAt_ty pre frame sl0)._1) x post_SF
         <==> tree_ens (repr_SF_of_ST f s_f (Fl.splitAt_ty pre frame sl0)._1) x post_SF')
      (fun () -> Fl.flist_extensionality post_SF post_SF' (fun i -> ()));

    assert (ens_equiv t s sl0 x sl1 <==> (
      (ST.tree_ens f sl0' x sl1' /\ sl_frame1 == sl_frame0)
    <==>
      (post_eq_src post_src_t sl0 sl1 /\
       tree_ens (repr_SF_of_ST f s_f (Fl.splitAt_ty pre frame sl0)._1) x post_SF')
    ));

    ens_eq_f sl0' sl1';

    let eq0 : prop = sl_frame1 == sl_frame0 /\ post_eq_src post_src_f sl0' sl1' in
    let eq1 : prop = post_eq_src post_src_t sl0 sl1                       in
    introduce (eq0 ==> eq1) /\ (eq1 ==> eq0)
    with introduce eq0 ==> eq1 with _ .
      introduce forall (i : Fin.fin (post_n + L.length frame) {Some? (post_src_t i)}) .
                  sl1 i === sl0 (Some?.v (post_src_t i))
      with begin
        Fl.append_index sl1' sl_frame1 i;
        if i < post_n
        then begin
          post_eq_srcD post_src_f sl0' sl1' i;
          Fl.append_index sl0' sl_frame1 (Some?.v (post_src_f i))
        end else begin
          assert (sl1 i === sl_frame1 (i - post_n));
          Fl.append_index sl0' sl_frame0 (i - post_n + L.length pre);
          assert (sl0 (Some?.v (post_src_t i)) === sl_frame0 (i - post_n))
        end
      end
    and introduce eq1 ==> eq0 with _ .
      introduce sl_frame1 == sl_frame0 /\ post_eq_src post_src_f sl0' sl1'
      with Fl.flist_extensionality sl_frame1 sl_frame0 begin fun i ->
        post_eq_srcD post_src_t sl0 sl1 (i + post_n);
        Fl.append_index sl1' sl_frame1 (i + post_n);
        Fl.append_index sl0' sl_frame0 (i + L.length pre)
      end and
      introduce forall (i : Fin.fin post_n {Some? (post_src_f i)}) .
                  sl1' i === sl0' (Some?.v (post_src_f i))
      with begin
        post_eq_srcD post_src_t sl0 sl1 i;
        Fl.append_index sl1' sl_frame1 i;
        Fl.append_index sl0' sl_frame0 (Some?.v (post_src_f i))
      end
#pop-options


#push-options "--z3rlimit 20"
// Quite long
let repr_SF_of_ST_req__Tbind a b pre (itm : ST.post_t a) post
      f (g : (x : a) -> ST.prog_tree b (itm x) post)
      (itm_n  : nat {ST.post_has_len itm itm_n})
      (post_n : nat {ST.post_has_len post post_n})
      (shp_f : ST.shape_tree _     itm_n  {ST.prog_has_shape f shp_f})
      (shp_g : ST.shape_tree itm_n post_n {forall (x : a) . ST.prog_has_shape (g x) shp_g})
      sl0
      (req_eq_g : (x : a) -> (sl1 : Fl.flist (itm x)) ->
                  Lemma (req_equiv (g x) (ST.mk_prog_shape (g x) shp_g) sl1))
      (ens_eq_f : (x : a) -> (sl1 : Fl.flist (itm x)) ->
                  Lemma (ens_equiv f (ST.mk_prog_shape f shp_f) sl0 x sl1))
  : Lemma
      (requires ST.tree_req f sl0 <==> tree_req (repr_SF_of_ST f (ST.mk_prog_shape f shp_f) sl0))
      (ensures  req_equiv (ST.Tbind a b pre itm post f g)
                          (ST.mk_prog_shape _ (ST.Sbind _ _ _ shp_f shp_g)) sl0)
  =
    let t = ST.Tbind a b pre itm post f g                                         in
    let s = ST.mk_prog_shape t (ST.Sbind (L.length pre) itm_n post_n shp_f shp_g) in
    let s_f = ST.mk_prog_shape f shp_f                                            in
    let s_g (x : a) = ST.mk_prog_shape (g x) shp_g                                in
    let r_f = repr_SF_of_ST f s_f sl0                                             in
    let r_g (x : a) (sl1 : Fl.flist (itm x)) = repr_SF_of_ST (g x) (s_g x) sl1    in
    let itm' = post_SF_of_ST itm s_f.shp                                          in

    assert (req_equiv t s sl0 == (
      (ST.tree_req f sl0 /\
      (forall (x : a) (sl1 : Fl.flist (itm x)) .
        ST.tree_ens f sl0 x sl1 ==> ST.tree_req (g x) sl1))
    <==>
      (tree_req r_f /\
      (forall (x : a) (sl1' : post_v itm' x) .
        tree_ens r_f x sl1' ==>
      (let sl1 = sel_ST_of_SF f s_f sl0 x sl1' in
        tree_req (r_g x sl1) /\
      (forall (y : b) (sl2' : post_v (post_SF_of_ST post #(L.length (itm x)) shp_g) y) .
        tree_ens (r_g x sl1) y sl2' ==> True))))
    )) by T.(trefl ());

    introduce forall (x : a) . ST.tree_req f sl0 ==> (
      (forall (sl1 : Fl.flist (itm x)) . ST.tree_ens f sl0 x sl1 ==> ST.tree_req (g x) sl1) <==>
      (forall (sl1' : post_v itm' x) .
        tree_ens r_f x sl1' ==>
        tree_req (r_g x (sel_ST_of_SF f s_f sl0 x sl1'))))
      with introduce _ ==> _
      with _ . begin
        introduce forall (sl1 : Fl.flist (itm x)) . ens_equiv f s_f sl0 x sl1
          with ens_eq_f x sl1;
        FStar.Classical.forall_intro (post_eq_src_iff (post_src_of_shape f s_f x) (post_bij s_f.shp) sl0);
        forall_morph_iff #(post_v itm' x)
          (fun sl1' -> ST.tree_ens f sl0 x (sel_ST_of_SF f s_f sl0 x sl1') ==>
                    ST.tree_req (g x) (sel_ST_of_SF f s_f sl0 x sl1'))
          (fun sl1' -> tree_ens r_f x sl1' ==>
                    tree_req (r_g x (sel_ST_of_SF f s_f sl0 x sl1')))
          (fun sl1' -> ens_equiv_rev f s_f sl0 x sl1';
                    req_eq_g x (sel_ST_of_SF f s_f sl0 x sl1'))
      end
#pop-options

#push-options "--z3rlimit 60"
let repr_SF_of_ST_ens__Tbind a b pre (itm : ST.post_t a) post
      f (g : (x : a) -> ST.prog_tree b (itm x) post)
      (itm_n  : nat {ST.post_has_len itm itm_n})
      (post_n : nat {ST.post_has_len post post_n})
      (shp_f : ST.shape_tree _     itm_n  {ST.prog_has_shape f shp_f})
      (shp_g : ST.shape_tree itm_n post_n {forall (x : a) . ST.prog_has_shape (g x) shp_g})
      sl0 y sl2
      (ens_eq_f : (x : a) -> (sl1 : Fl.flist (itm x)) ->
                  Lemma (ens_equiv f (ST.mk_prog_shape f shp_f) sl0 x sl1))
      (ens_eq_g : (x : a) -> (sl1 : Fl.flist (itm x)) ->
                  Lemma (ens_equiv (g x) (ST.mk_prog_shape (g x) shp_g) sl1 y sl2))
  : Lemma
      (ensures  ens_equiv (ST.Tbind a b pre itm post f g)
                          (ST.mk_prog_shape _ (ST.Sbind _ _ _ shp_f shp_g)) sl0 y sl2)
  =
    let t = ST.Tbind a b pre itm post f g                                         in
    let s = ST.mk_prog_shape t (ST.Sbind (L.length pre) itm_n post_n shp_f shp_g) in
    let s_f = ST.mk_prog_shape f shp_f                                            in
    let s_g (x : a) = ST.mk_prog_shape (g x) shp_g                                in
    let r_f = repr_SF_of_ST f s_f sl0                                             in
    let r_g (x : a) (sl1 : Fl.flist (itm x)) = repr_SF_of_ST (g x) (s_g x) sl1    in
    let itm'  = post_SF_of_ST itm s_f.shp                                         in
    let post'g = post_SF_of_ST post shp_g                                         in
    let post'  = post_SF_of_ST post s.shp                                         in
    let sl2' : post_v post' y = sel_SF_of_ST post s.shp y sl2                     in
    let post_src_t = post_src_of_shape t s y                                      in
    let post_src_f (x : a)  = post_src_of_shape f s_f x                           in
    let post_src_g (x : a) = post_src_of_shape (g x) (s_g x) y                    in

    assert (ens_equiv t s sl0 y sl2 ==
      ((exists (x : a) (sl1 : Fl.flist (itm x)) .
         ST.tree_ens f sl0 x sl1 /\ ST.tree_ens (g x) sl1 y sl2)
     <==>
      (post_eq_src post_src_t sl0 sl2 /\
      ((exists (x : a) (sl1' : post_v itm' x) .
         tree_ens r_f x sl1' /\
       (let sl1 = sel_ST_of_SF f s_f sl0 x sl1' in
        let r_g = r_g x sl1                     in
        (exists (yg : b) (sl2g : post_v (post_SF_of_ST post #(L.length (itm x)) shp_g) yg) .
         tree_ens r_g yg sl2g /\
        (let sl2f : Fl.flist (post yg) = sel_ST_of_SF (g x) (s_g x) sl1 yg sl2g in
         tree_ens (Tret b yg post' (Fl.dlist_of_f (sel_SF_of_ST post s.shp yg sl2f))) y sl2'
         ))))))
    )) by T.(trefl ());

    assert (post_eq_src post_src_t sl0 sl2);

    introduce forall (x : a) .
       (exists (sl1 : Fl.flist (itm x)) . ST.tree_ens f sl0 x sl1 /\ ST.tree_ens (g x) sl1 y sl2)
    <==> (exists (sl1' : post_v itm' x) .
         tree_ens r_f x sl1' /\
       (let sl1 = sel_ST_of_SF f s_f sl0 x sl1' in
        let r_g = r_g x sl1 in
        (exists (sl2g : post_v post'g y) .
         tree_ens r_g y sl2g /\
         sl2' == sel_SF_of_ST post s.shp y (sel_ST_of_SF (g x) (s_g x) sl1 y sl2g)
         )))
    with begin
      introduce forall (sl2g : post_v post'g y) (sl1 : Fl.flist (itm x)) .
        sl2' == sel_SF_of_ST post s.shp y (sel_ST_of_SF (g x) (s_g x) sl1 y sl2g)
        <==> (sl2g == sel_SF_of_ST post shp_g y sl2 /\
           post_eq_src (post_src_g x) sl1 sl2)
      with begin
        let sl2gST = sel_ST_of_SF (g x) (s_g x) sl1 y sl2g in
        // [sel_SF_of_ST post s y] is injective (for s = [Sbind _]), the inverse is sel_ST_of_SF
        U.assert_by (sel_SF_of_ST post s.shp y sl2 == sel_SF_of_ST post s.shp y sl2gST
                  ==> sl2 == sl2gST)
          (fun () -> post_eq_src_ST_SF_ST post_src_t (post_bij s.shp) sl0 sl2;
                  post_eq_src_ST_SF_ST post_src_t (post_bij s.shp) sl0 sl2gST);
        sel_SF_ST_SF  (g x) (s_g x) sl1 y sl2g;
        post_eq_src_iff (post_src_g x) (post_bij shp_g) sl1 sl2
      end;

      FStar.Classical.forall_intro (ens_eq_f x);
      FStar.Classical.forall_intro (post_eq_src_iff (post_src_f x) (post_bij shp_f) sl0);

      exists_morph_iff #(post_v itm' x)
        (fun sl1' -> ST.tree_ens f sl0 x (sel_ST_of_SF f s_f sl0 x sl1') /\
                  ST.tree_ens (g x) (sel_ST_of_SF f s_f sl0 x sl1') y sl2)
        (fun sl1' -> tree_ens r_f x sl1' /\
                 (let sl1 = sel_ST_of_SF f s_f sl0 x sl1' in
                  let r_g = r_g x sl1                     in
                  post_eq_src (post_src_g x) sl1 sl2 /\
                  tree_ens r_g y (sel_SF_of_ST post shp_g y sl2)))
        (fun sl1' ->
          let sl1 = sel_ST_of_SF f s_f sl0 x sl1' in
          ens_eq_f x sl1;
          ens_equiv_rev f s_f sl0 x sl1';
          FStar.Classical.move_requires (ens_eq_g x) sl1)
    end
#pop-options

let repr_SF_of_ST_ens__TbindP a b pre post
      wp (g : a -> ST.prog_tree b pre post)
      (post_n : nat {ST.post_has_len post post_n})
      (shp_g : ST.shape_tree _ post_n {forall (x : a) . ST.prog_has_shape (g x) shp_g})
      sl0 y sl1
      (ens_eq_g : (x : a) ->
                  Lemma (ens_equiv (g x) (ST.mk_prog_shape (g x) shp_g) sl0 y sl1))
  : Lemma
      (ensures ens_equiv (ST.TbindP a b pre post wp g)
                         (ST.mk_prog_shape _ (ST.SbindP _ _ shp_g)) sl0 y sl1)
  =
    let t = ST.TbindP a b pre post wp g                                in
    let s = ST.mk_prog_shape t (ST.SbindP (L.length pre) post_n shp_g) in
    let s_g (x : a) = ST.mk_prog_shape (g x) shp_g                     in
    let r_g (x : a) = repr_SF_of_ST (g x) (s_g x) sl0                  in
    let post'g = post_SF_of_ST post shp_g                              in
    let post'  = post_SF_of_ST post s.shp                              in
    let sl1' : post_v post' y = sel_SF_of_ST post s.shp y sl1          in
    let post_src_t = post_src_of_shape t s y                           in
    let post_src_g (x : a) = post_src_of_shape (g x) (s_g x) y         in


    assert (ens_equiv t s sl0 y sl1 == (
      ((exists (x : a) .
        as_ensures wp x /\ ST.tree_ens (g x) sl0 y sl1)
     <==>
      (post_eq_src post_src_t sl0 sl1 /\
      (exists (x : a) .
       as_ensures wp x /\
      (exists (yg : b) (sl1g : post_v (post_SF_of_ST post #(L.length #Type pre) shp_g) yg) .
       tree_ens (r_g x) yg sl1g /\
      (let sl1f = sel_ST_of_SF (g x) (s_g x) sl0 yg sl1g in
       y == yg /\ sl1' == Fl.flist_of_d (Fl.dlist_of_f (sel_SF_of_ST post s.shp yg sl1f))
      )))))
    )) by T.(norm normal_equiv; trefl ());

    assert (post_eq_src post_src_t sl0 sl1);
  
    introduce forall (x : a {as_ensures wp x}) .
      (ST.tree_ens (g x) sl0 y sl1 <==>
      (exists (sl1g : post_v post'g y) .
         tree_ens (r_g x) y sl1g /\
         sl1' == sel_SF_of_ST post s.shp y (sel_ST_of_SF (g x) (s_g x) sl0 y sl1g)))
    with begin
      introduce forall (sl1g : post_v post'g y) .
        sl1' == sel_SF_of_ST post s.shp y (sel_ST_of_SF (g x) (s_g x) sl0 y sl1g)
        <==> (sl1g == sel_SF_of_ST post shp_g y sl1 /\
            post_eq_src (post_src_g x) sl0 sl1)
       with begin
        let sl1gST = sel_ST_of_SF (g x) (s_g x) sl0 y sl1g in
         U.assert_by (sel_SF_of_ST post s.shp y sl1 == sel_SF_of_ST post s.shp y sl1gST
                   ==> sl1 == sl1gST)
          (fun () -> post_eq_src_ST_SF_ST post_src_t (post_bij s.shp) sl0 sl1;
                  post_eq_src_ST_SF_ST post_src_t (post_bij s.shp) sl0 sl1gST);
        sel_SF_ST_SF (g x) (s_g x) sl0 y sl1g;
        post_eq_src_iff (post_src_g x) (post_bij shp_g) sl0 sl1
       end;
       ens_eq_g x
    end

let case_bool (#goal : bool -> Type) (c_true : goal true) (c_false : goal false)
  : (b : bool) -> goal b
  = fun b -> if b then c_true else c_false

let repr_SF_of_ST_req__Tif a pre post
      (thn els : ST.prog_tree a pre post)
      (post_n : nat {ST.post_has_len post post_n})
      (shp_thn : ST.shape_tree _ post_n {ST.prog_has_shape thn shp_thn})
      (shp_els : ST.shape_tree _ post_n {ST.prog_has_shape els shp_els})
      sl0
      (req_eq_thn : squash (req_equiv thn (ST.mk_prog_shape thn shp_thn) sl0))
      (req_eq_els : squash (req_equiv els (ST.mk_prog_shape els shp_els) sl0))
      guard
  : Lemma (req_equiv (ST.Tif a guard pre post thn els)
                     (ST.mk_prog_shape _ (ST.Sif _ _ shp_thn shp_els)) sl0)
  =
    calc (<==>) {
      ST.tree_req (ST.Tif a guard pre post thn els) sl0;
    <==> { _ by T.(clear_top (); clear_top (); revert(*guard*)();
                 apply (`case_bool);
                 let _ = repeatn 2 (fun () -> norm normal_equiv; smt ()) in ()) }
      tree_req (repr_SF_of_ST (ST.Tif a guard pre post thn els)
                              (ST.mk_prog_shape _ (ST.Sif _ _ shp_thn shp_els)) sl0);
    }

// TODO? generalize and use for other cases
#push-options "--ifuel 0"
let repr_SF_of_ST_ens__add_ret #a #pre #post
      (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (shp' : ST.shape_tree (L.length pre) s.post_len)
      (sl0 : Fl.flist pre) (x : a) (sl1 : Fl.flist (post x))
      (t_eq : squash (ens_equiv t s sl0 x sl1))
      (sub  : (i : Fin.fin s.post_len) -> Lemma
                (requires Some? (post_src_f_of_shape shp' i))
                (ensures  post_src_of_shape t s x i == post_src_f_of_shape shp' i))
   : Lemma (
       post_src_well_typed pre (post x) (post_src_f_of_shape shp') /\ (
       ST.tree_ens t sl0 x sl1 <==>
       (post_eq_src (post_src_f_of_shape shp') sl0 sl1 /\
        tree_ens (Tbind a a (post_SF_of_ST post s.shp) _ (repr_SF_of_ST t s sl0) (fun x' sl1' ->
                  let sl1_0 = sel_ST_of_SF t s sl0 x' sl1' in
                  return_SF_post_of_ST post shp' x' sl1_0))
          x (sel_SF_of_ST post shp' x sl1))))
   =
     U.assert_by (post_src_well_typed pre (post x) (post_src_f_of_shape shp'))
       (fun () -> FStar.Classical.forall_intro (post_src_of_shape_ty t s x);
               FStar.Classical.forall_intro (FStar.Classical.move_requires sub));
     calc (<==>) {
       ST.tree_ens t sl0 x sl1;
     <==> { t_eq }
       post_eq_src (post_src_of_shape t s x) sl0 sl1 /\
       tree_ens (repr_SF_of_ST t s sl0) x (sel_SF_of_ST post s.shp x sl1);
     };
     introduce forall sl1' . post_eq_src (post_src_of_shape t s x) sl0 sl1' ==>
                        post_eq_src (post_src_f_of_shape shp') sl0 sl1'
       with FStar.Classical.forall_intro (FStar.Classical.move_requires sub);

     introduce post_eq_src (post_src_f_of_shape shp') sl0 sl1 ==>
               (ST.tree_ens t sl0 x sl1 <==>
                tree_ens (Tbind a a (post_SF_of_ST post s.shp) _ (repr_SF_of_ST t s sl0) (fun x' sl1' ->
                          let sl1_0 = sel_ST_of_SF t s sl0 x' sl1' in
                          return_SF_post_of_ST post shp' x' sl1_0))
                   x (sel_SF_of_ST post shp' x sl1))
     with _ . begin
       calc (<==>) {
         tree_ens (Tbind a a (post_SF_of_ST post s.shp) _ (repr_SF_of_ST t s sl0) (fun x sl1' ->
                         let sl1_0 = sel_ST_of_SF t s sl0 x sl1' in
                         return_SF_post_of_ST post shp' x sl1_0))
                  x (sel_SF_of_ST post shp' x sl1);
       == { _ by T.(norm normal_equiv; trefl ()) }
         exists (x' : a) (sl1' : post_v (post_SF_of_ST post s.shp) x') .
           tree_ens (repr_SF_of_ST t s sl0) x' sl1' /\
           (x == x' /\
           sel_SF_of_ST post shp' x sl1 == Fl.flist_of_d (Fl.dlist_of_f (
             sel_SF_of_ST post shp' x' (sel_ST_of_SF t s sl0 x' sl1'))));
       <==> { introduce forall (sl1' : post_v (post_SF_of_ST post s.shp) x) .
                sel_SF_of_ST post shp' x sl1 == sel_SF_of_ST post shp' x (sel_ST_of_SF t s sl0 x sl1') ==>
                sl1 == sel_ST_of_SF t s sl0 x sl1'
              with (
                let src = post_src_f_of_shape shp' in
                let bij = post_bij shp'            in
                post_eq_src_ST_SF_ST src bij sl0 sl1; (* using post_eq_src src sl0 sl1 *)
                sell_ST_of_SF_eq_src (post_src_of_shape t s x) (post_bij s.shp) sl0 sl1';
                post_eq_src_ST_SF_ST src bij sl0 (sel_ST_of_SF t s sl0 x sl1')
          )}
         exists (sl1' : post_v (post_SF_of_ST post s.shp) x) .
           tree_ens (repr_SF_of_ST t s sl0) x sl1' /\
           sl1 == sel_ST_of_SF t s sl0 x sl1';
       <==> { FStar.Classical.forall_intro (sel_SF_ST_SF t s sl0 x);
            FStar.Classical.forall_intro (post_eq_src_iff (post_src_of_shape t s x) (post_bij s.shp) sl0) }
         tree_ens (repr_SF_of_ST t s sl0) x (sel_SF_of_ST post s.shp x sl1) /\
         post_eq_src (post_src_of_shape t s x) sl0 sl1;
       }
     end
#pop-options

#push-options "--ifuel 1 --z3rlimit 20"
let repr_SF_of_ST_ens__Tif a guard pre post
      (thn els : ST.prog_tree a pre post)
      (post_n : nat {ST.post_has_len post post_n})
      (shp_thn : ST.shape_tree _ post_n {ST.prog_has_shape thn shp_thn})
      (shp_els : ST.shape_tree _ post_n {ST.prog_has_shape els shp_els})
      sl0 x sl1
      (ens_eq_thn : squash (ens_equiv thn (ST.mk_prog_shape thn shp_thn) sl0 x sl1))
      (ens_eq_els : squash (ens_equiv els (ST.mk_prog_shape els shp_els) sl0 x sl1))
  : Lemma (ens_equiv (ST.Tif a guard pre post thn els)
                     (ST.mk_prog_shape _ (ST.Sif _ _ shp_thn shp_els)) sl0 x sl1)
  =
    let t = ST.Tif a guard pre post thn els                                   in
    let s = ST.mk_prog_shape t (ST.Sif (L.length pre) post_n shp_thn shp_els) in
    let s_thn = ST.mk_prog_shape thn shp_thn                                  in
    let s_els = ST.mk_prog_shape els shp_els                                  in
    let goal (guard : bool) : prop =
      ens_equiv (ST.Tif a guard pre post thn els)
                (ST.mk_prog_shape _ (ST.Sif _ _ shp_thn shp_els)) sl0 x sl1
    in
    U.assert_by (post_src_well_typed pre (post x) (post_src_f_of_shape s.shp))
      (fun () -> FStar.Classical.forall_intro (post_src_of_shape_ty t s x));
    if guard
    then begin
      assert (goal true == (
        ST.tree_ens thn sl0 x sl1 <==>
       (post_eq_src (post_src_f_of_shape s.shp) sl0 sl1 /\
        tree_ens (Tbind a a (post_SF_of_ST post shp_thn) _
                 (repr_SF_of_ST thn s_thn sl0) (fun x sl1' ->
                 let sl1_0 = sel_ST_of_SF thn s_thn sl0 x sl1' in
                 return_SF_post_of_ST post s.shp x sl1_0))
                 x (sel_SF_of_ST post s.shp x sl1))
      )) by T.(norm normal_equiv; trefl ());
      repr_SF_of_ST_ens__add_ret thn s_thn s.shp sl0 x sl1
        ens_eq_thn (fun i -> ())
   end else begin
     assert (goal false == (
        ST.tree_ens els sl0 x sl1 <==>
       (post_eq_src (post_src_f_of_shape s.shp) sl0 sl1 /\
        tree_ens (Tbind a a (post_SF_of_ST post shp_els) _
                 (repr_SF_of_ST els s_els sl0) (fun x sl1' ->
                 let sl1_0 = sel_ST_of_SF els s_els sl0 x sl1' in
                 return_SF_post_of_ST post s.shp x sl1_0))
                 x (sel_SF_of_ST post s.shp x sl1))
      )) by T.(norm normal_equiv; trefl ());
      repr_SF_of_ST_ens__add_ret els s_els s.shp sl0 x sl1
        ens_eq_els (fun i -> ())
   end
#pop-options


#push-options " --ifuel 0 --z3rlimit 10"
let rec repr_SF_of_ST_req
  (#a : Type) (#pre : ST.pre_t) (#post : ST.post_t a)
  (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
  (sl0 : Fl.flist pre)
  : Lemma (ensures req_equiv t s sl0) (decreases t)
  = ST.match_prog_tree t
    (fun a pre post t -> (s : ST.prog_shape t) -> (sl0 : Fl.flist pre) ->
       squash (ST.tree_req t sl0 <==> tree_req (repr_SF_of_ST t s sl0)))
    (fun (*ST.Tequiv*) pre post0 e -> fun s sl0 -> ())
    begin fun (*ST.Tframe*) a pre post frame f -> fun s sl0 ->
      let ST.Sframe pre_n post_n frame_n shp_f = s.shp           in 
      let sl0' : Fl.flist pre = (Fl.splitAt_ty pre frame sl0)._1 in
      repr_SF_of_ST_req f (ST.mk_prog_shape f shp_f) sl0'
    end
    (fun (*ST.Tspec*) a pre post req ens -> fun s sl0 -> ())
    (fun (*ST.Tret*) a x post -> fun s sl0 -> ())
    begin fun (*ST.Tbind*) a b pre itm post f g -> fun s sl0 ->
      let ST.Sbind _ itm_n post_n shp_f shp_g = s.shp in
      let s_f = ST.mk_prog_shape f shp_f              in
      let s_g (x : a) = ST.mk_prog_shape (g x) shp_g  in
      repr_SF_of_ST_req f s_f sl0;
      repr_SF_of_ST_req__Tbind a b pre itm post f g itm_n post_n shp_f shp_g sl0
        (fun x sl1 -> repr_SF_of_ST_req (g x) (s_g x) sl1)
        (fun x sl1 -> repr_SF_of_ST_ens f s_f sl0 x sl1)
    end
    begin fun (*ST.TbindP*) a b pre post wp g -> fun s sl0 ->
      let ST.SbindP _ post_n shp_g = s.shp           in
      let s_g (x : a) = ST.mk_prog_shape (g x) shp_g in
      let pt0 x = ST.tree_req (g x) sl0              in
      let pt1 x = tree_req (repr_SF_of_ST (g x) (s_g x) sl0) /\
                    (forall (y : b) (sl1' : post_v (post_SF_of_ST post #(L.length #Type pre) shp_g) y) .
                    tree_ens (repr_SF_of_ST (g x) (s_g x) sl0) y sl1' ==> True) in
      calc (<==>) {
        ST.tree_req (ST.TbindP a b pre post wp g) sl0;
      <==> { _ by T.(apply_lemma (`U.iff_refl); trefl ()) }
        wp (fun x -> ST.tree_req (g x) sl0);
      <==> {}
        wp pt0;
      <==> { wp_morph_iff wp pt0 pt1 (fun x -> repr_SF_of_ST_req (g x) (s_g x) sl0) }
        wp pt1;
      <==> {}
        wp (fun x -> tree_req (repr_SF_of_ST (g x) (ST.mk_prog_shape (g x) shp_g) sl0) /\
                (forall (y : b) (sl1' : post_v (post_SF_of_ST post #(L.length #Type pre) shp_g) y) .
                tree_ens (repr_SF_of_ST (g x) (ST.mk_prog_shape (g x) shp_g) sl0) y sl1' ==> True));
      <==> { _ by T.(apply_lemma (`U.iff_refl); trefl ())}
        tree_req (repr_SF_of_ST (ST.TbindP a b pre post wp g)
                                 (ST.mk_prog_shape _ (ST.SbindP _ _ shp_g)) sl0);
      }
    end
    begin fun (*ST.Tif*) a guard pre post thn els -> fun s sl0 ->
      let ST.Sif _ post_n shp_thn shp_els = s.shp in
      repr_SF_of_ST_req__Tif
        a pre post thn els post_n shp_thn shp_els sl0
        (repr_SF_of_ST_req thn (ST.mk_prog_shape thn shp_thn) sl0)
        (repr_SF_of_ST_req els (ST.mk_prog_shape els shp_els) sl0)
        guard
    end s sl0

and repr_SF_of_ST_ens
  (#a : Type) (#pre : ST.pre_t) (#post : ST.post_t a)
  (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
  (sl0 : Fl.flist pre) (res : a) (sl1 : Fl.flist (post res))
  : Lemma (ensures ens_equiv t s sl0 res sl1)
          (decreases t)
  = ST.match_prog_tree t
    (fun a pre post t -> (s : ST.prog_shape t) ->
       (sl0 : Fl.flist pre) -> (res : a) -> (sl1 : Fl.flist (post res)) ->
       squash (ens_equiv t s sl0 res sl1))
    begin fun (*ST.Tequiv*) pre post0 e -> fun s sl0 U.Unit' sl1 ->
      repr_SF_of_ST_ens__Tequiv pre post0 e sl0 sl1
    end
    begin fun (*ST.Tframe*) a pre post frame f -> fun s sl0 x sl1 ->
      let ST.Sframe pre_n post_n frame_n shp_f = s.shp in 
      repr_SF_of_ST_ens__Tframe a pre post frame f post_n shp_f sl0 x sl1
        (fun sl0' sl1' -> repr_SF_of_ST_ens f (ST.mk_prog_shape f shp_f) sl0' x sl1')
    end
    begin fun (*ST.Tspec*) a pre post req ens -> fun s sl0 x sl1 ->
      let ST.Sspec pre_n post_n = s.shp in
      post_SF_of_ST__spec post pre_n post_n;
      Fl.flist_extensionality (sel_SF_of_ST post s.shp x sl1) sl1 (fun _ -> ())
    end
    begin fun (*ST.Tret*) a x post -> fun s sl0 x sl1 ->
      let ST.Sret smp_ret post_n = s.shp in
      post_SF_of_ST__ret post smp_ret post_n;
      Fl.flist_extensionality (sel_SF_of_ST post s.shp x sl1) sl1 (fun _ -> ())
    end
    begin fun (*ST.Tbind*) a b pre itm post f g -> fun s sl0 y sl2 ->
      let ST.Sbind _ itm_n post_n shp_f shp_g = s.shp in
      let s_f = ST.mk_prog_shape f shp_f              in
      let s_g (x : a) = ST.mk_prog_shape (g x) shp_g  in
      repr_SF_of_ST_ens__Tbind a b pre itm post f g itm_n post_n shp_f shp_g sl0 y sl2
        (fun x sl1 -> repr_SF_of_ST_ens f s_f sl0 x sl1)
        (fun x sl1 -> repr_SF_of_ST_ens (g x) (s_g x) sl1 y sl2)
    end
    begin fun (*ST.TbindP*) a b pre post wp g -> fun s sl0 y sl1 ->
      let ST.SbindP _ post_n shp_g = s.shp           in
      let s_g (x : a) = ST.mk_prog_shape (g x) shp_g in
      repr_SF_of_ST_ens__TbindP a b pre post wp g post_n shp_g sl0 y sl1
        (fun x -> repr_SF_of_ST_ens (g x) (s_g x) sl0 y sl1)
    end
    begin fun (*ST.Tif*) a guard pre post thn els -> fun s sl0 x sl1 ->
      let ST.Sif _ post_n shp_thn shp_els = s.shp in
      repr_SF_of_ST_ens__Tif
        a guard pre post thn els post_n shp_thn shp_els sl0 x sl1
        (repr_SF_of_ST_ens thn (ST.mk_prog_shape thn shp_thn) sl0 x sl1)
        (repr_SF_of_ST_ens els (ST.mk_prog_shape els shp_els) sl0 x sl1)
    end s sl0 res sl1
#pop-options

#push-options "--ifuel 0 --fuel 0"
let repr_SF_of_ST_rall_equiv
      (#a : Type) (#pre : ST.pre_t) (#post : ST.post_t a)
      (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Fl.flist pre)
  : Lemma ((ST.tree_req t sl0 <==> tree_req (repr_SF_of_ST_rall t s sl0)) /\
           (forall (x : a) (sl1 : Fl.flist (post x)) .
             ST.tree_ens t sl0 x sl1 <==> tree_ens (repr_SF_of_ST_rall t s sl0) x sl1))
  =
    calc (<==>) {
      tree_req (repr_SF_of_ST_rall t s sl0);
    <==> { _ by T.(apply_lemma (`U.iff_refl); trefl ()) }
      tree_req (repr_SF_of_ST t s sl0) /\
        (forall x sl1' . tree_ens (repr_SF_of_ST t s sl0) x sl1' ==> True);
    <==> { }
      tree_req (repr_SF_of_ST t s sl0);
    <==> { repr_SF_of_ST_req t s sl0 }
      ST.tree_req t sl0;
    };

    introduce forall (x : a) (sl1 : Fl.flist (post x)) .
        ST.tree_ens t sl0 x sl1 <==> tree_ens (repr_SF_of_ST_rall t s sl0) x sl1
    with begin
      calc (<==>) {
        tree_ens (repr_SF_of_ST_rall t s sl0) x sl1;
      <==> { _ by T.(apply_lemma (`U.iff_refl); trefl ()) }
        exists x' (sl1' : post_v (post_SF_of_ST post s.shp) x') .
          tree_ens (repr_SF_of_ST t s sl0) x' sl1' /\
         (x == x' /\ sl1 == Fl.flist_of_d (Fl.dlist_of_f (sel_ST_of_SF t s sl0 x' sl1')));
      <==> { }
        exists (sl1' : post_v (post_SF_of_ST post s.shp) x) .
        tree_ens (repr_SF_of_ST t s sl0) x sl1' /\ sl1 == sel_ST_of_SF t s sl0 x sl1';
      <==> { FStar.Classical.forall_intro (sel_SF_ST_SF t s sl0 x);
           FStar.Classical.forall_intro (post_eq_src_iff (post_src_of_shape t s x) (post_bij s.shp) sl0) }
        tree_ens (repr_SF_of_ST t s sl0) x (sel_SF_of_ST post s.shp x sl1) /\
        post_eq_src (post_src_of_shape t s x) sl0 sl1;
      <==> { repr_SF_of_ST_ens t s sl0 x sl1 }
        ST.tree_ens t sl0 x sl1;
      }
    end
#pop-options

#pop-options
