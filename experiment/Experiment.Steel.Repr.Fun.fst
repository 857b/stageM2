module Experiment.Steel.Repr.Fun

module T = FStar.Tactics
open FStar.Calc
open Learn.Logic

(*** Repr.ST --> Repr.Fun *)

(**) let __begin_repr_fun_of_st = ()

let rec post_src_of_shape_ty
      (#a : Type) (#pre0 : ST.pre_t) (#post0 : ST.post_t a) (t : ST.prog_tree a pre0 post0)
      (s : ST.prog_shape t) (x : a) (i : Fin.fin (L.length (post0 x)) {Some? (post_src_f_of_shape s.shp i)})
  : Lemma (ensures  L.index (post0 x) i == L.index pre0 (Some?.v (post_src_f_of_shape s.shp i)))
          (decreases t)
  = match t with
    | ST.Tequiv _ _ _ -> ()
    | ST.Tframe a pre post frame f ->
             let Sframe _ post_n _ s_f = s.shp in
             Ll.append_index (post x) frame i;
             if i < post_n
             then begin
               let Some j = post_src_f_of_shape s_f i in
               Ll.append_index pre frame j;
               post_src_of_shape_ty f (ST.mk_prog_shape f s_f) x i
             end else Ll.append_index pre frame (i - post_n + L.length pre)
    | ST.Tspec  _ pre post _ _ -> ()
    | ST.Tret _ _ _ | ST.Tbind _ _  _ _ _  _ _ | ST.TbindP _ _  _ _  _ _ _ -> ()

#push-options "--z3rlimit 20"
let sell_Fun_ST_Fun
      (#pre #post : Fl.ty_list)
      (s : post_src pre post) (bij : post_bij_t s)
      (sl0 : Fl.flist pre) (sl1_Fun : Fl.flist (postl_Fun_of_ST post bij))
  : Lemma (sell_Fun_of_ST post bij (sell_ST_of_Fun s bij sl0 sl1_Fun) == sl1_Fun)
  = Fl.flist_extensionality
         (sell_Fun_of_ST post bij (sell_ST_of_Fun s bij sl0 sl1_Fun)) sl1_Fun
    begin fun i ->
      let sl1_ST = sell_ST_of_Fun s bij sl0 sl1_Fun in
      calc (==) {
        sell_Fun_of_ST post bij sl1_ST i;
      == {_ by T.(trefl ())}
        U.cast (L.index (postl_Fun_of_ST post bij) i)
          (sl1_ST (bij.idx_ST i));
      == {}
        sl1_Fun (bij.idx_Fun (bij.idx_ST i));
      == {}
        sl1_Fun i;
      }
   end
#pop-options


let post_Fun_of_ST__frame
      (#a : Type) (post : ST.post_t a) (frame: Fl.ty_list)
      (pre_n : nat) (post_n : nat {post_has_len post post_n}) (f : shape_tree pre_n post_n)
  : Lemma (post_Fun_of_ST (ST.frame_post post frame) (Sframe pre_n post_n (L.length frame) f)
                == post_Fun_of_ST post f)
  = 
    let post0 = post_Fun_of_ST (ST.frame_post post frame) (Sframe pre_n post_n (L.length frame) f) in
    let post1 = post_Fun_of_ST post f in
    U.funext_eta post0 post1
         (assert (post0 == U.eta post0) by T.(trefl ()))
         (assert (post1 == U.eta post1) by T.(trefl ()))
         (fun x -> Ll.list_extensionality (post0 x) (post1 x)
           (fun i -> Ll.append_index (post x) frame ((post_bij f).idx_ST i)))

// TODO: factorize
let post_Fun_of_ST__spec #a post pre_n post_n
  =
    let post' = post_Fun_of_ST post (Sspec pre_n post_n) in
    U.funext_eta post' (U.eta post)
         (assert (post' == U.eta post') by T.(trefl ())) (_ by T.(trefl ()))
         (fun x -> Ll.list_extensionality (post' x) (post x) (fun i -> ()))

let post_Fun_of_ST__ret #a post post_n
  =
    let post' = post_Fun_of_ST post (Sret post_n) in
    U.funext_eta post' (U.eta post)
         (assert (post' == U.eta post') by T.(trefl ())) (_ by T.(trefl ()))
         (fun x -> Ll.list_extensionality (post' x) (post x) (fun i -> ()))


(**) let __end_repr_fun_of_st = ()


(***** soundness of ST --> Fun *)

#push-options "--fuel 1 --ifuel 0"

let sell_ST_of_Fun_eq_src #pre #post s bij sl0 sl1_Fun = ()

#push-options "--z3rlimit 10"
let post_eq_src_ST_Fun_ST
      (#pre #post : Fl.ty_list)
      (s : post_src pre post) (bij : post_bij_t s)
      (sl0 : Fl.flist pre) (sl1_ST : Fl.flist post)
  : Lemma (requires post_eq_src s sl0 sl1_ST)
          (ensures  sell_ST_of_Fun s bij sl0 (sell_Fun_of_ST post bij sl1_ST) == sl1_ST)
  =
    Fl.flist_extensionality (sell_ST_of_Fun s bij sl0 (sell_Fun_of_ST post bij sl1_ST)) sl1_ST
    begin fun i ->
      match s i with
      | Some j -> calc (==) {
                   sell_ST_of_Fun s bij sl0 (sell_Fun_of_ST post bij sl1_ST) i;
                 == {}
                   U.cast (L.index post i) (sl0 j);
                 == {(* by [post_eq_src] *)}
                   sl1_ST i;
                 }
      | None -> ()
    end
#pop-options



#push-options "--z3rlimit 10"
let repr_Fun_of_ST_ens__Tframe a pre post frame f
      (post_n : nat {ST.post_has_len post post_n})
      (shp_f : ST.shape_tree _ post_n {ST.prog_has_shape f shp_f})
      sl0 x sl1
      (ens_eq_f : (sl0' : Fl.flist pre) -> (sl1' : Fl.flist (post x)) ->
                  Lemma (ens_equiv f (ST.mk_prog_shape f shp_f) sl0' x sl1'))
  : Lemma (ensures ens_equiv (ST.Tframe a pre post frame f)
                             (ST.mk_prog_shape _ (Sframe _ _ (L.length frame) shp_f)) sl0 x sl1)
  =
    post_Fun_of_ST__frame post frame (L.length pre) post_n shp_f;
 
    let t = ST.Tframe a pre post frame f                                             in
    let s = ST.mk_prog_shape t (Sframe (L.length pre) post_n (L.length frame) shp_f) in
    let s_f = ST.mk_prog_shape f shp_f                                               in
    let post_Fun  = sel_Fun_of_ST (ST.frame_post post frame) s.shp x sl1             in
    let post_src_t = post_src_of_shape t s x                                         in

    assert (ens_equiv t s sl0 x sl1 == (
     (let sl0', frame0 = Fl.splitAt_ty pre      frame sl0 in
      let sl1', frame1 = Fl.splitAt_ty (post x) frame sl1 in
      frame1 == frame0 /\ ST.tree_ens f sl0' x sl1')
    <==>
      (post_eq_src post_src_t sl0 sl1 /\
       tree_ens (repr_Fun_of_ST t s sl0) x post_Fun)
    )) by T.(trefl ());

    assert (repr_Fun_of_ST t s sl0 == (
      repr_Fun_of_ST f s_f (Fl.splitAt_ty pre frame sl0)._1
    )) by T.(trefl ());
    
    let sl0', frame0 = Fl.splitAt_ty pre      frame sl0 in
    let sl1', frame1 = Fl.splitAt_ty (post x) frame sl1 in
    let post_Fun' = sel_Fun_of_ST post shp_f x sl1'     in
    let post_src_f = post_src_of_shape f s_f x          in
    let bij = post_bij shp_f                            in

    ens_eq_f sl0' sl1';
    Fl.flist_extensionality post_Fun post_Fun' (fun i -> ());

    let eq0 : prop = frame1 == frame0 /\ post_eq_src post_src_f sl0' sl1' in
    let eq1 : prop = post_eq_src post_src_t sl0 sl1                         in
    introduce (eq0 ==> eq1) /\ (eq1 ==> eq0)
    with introduce eq0 ==> eq1 with _ .
      introduce forall (i : Fin.fin (post_n + L.length frame) {Some? (post_src_t i)}) .
                  sl1 i === sl0 (Some?.v (post_src_t i))
      with begin
        Fl.append_index sl1' frame1 i;
        if i < post_n
        then begin
          post_eq_srcD post_src_f sl0' sl1' i;
          Fl.append_index sl0' frame0 (Some?.v (post_src_f i))
        end else begin
          assert (sl1 i === frame1 (i - post_n));
          Fl.append_index sl0' frame0 (i - post_n + L.length pre);
          assert (sl0 (Some?.v (post_src_t i)) === frame0 (i - post_n))
        end
      end
    and introduce eq1 ==> eq0 with _ .
      introduce frame1 == frame0 /\ post_eq_src post_src_f sl0' sl1'
      with Fl.flist_extensionality frame1 frame0 begin fun i ->
        post_eq_srcD post_src_t sl0 sl1 (i + post_n);
        Fl.append_index sl1' frame1 (i + post_n);
        Fl.append_index sl0' frame0 (i + L.length pre)
      end and
      introduce forall (i : Fin.fin post_n {Some? (post_src_f i)}) .
                  sl1' i === sl0' (Some?.v (post_src_f i))
      with begin
        post_eq_srcD post_src_t sl0 sl1 i;
        Fl.append_index sl1' frame1 i;
        Fl.append_index sl0' frame0 (Some?.v (post_src_f i))
      end
#pop-options


#push-options "--z3rlimit 20"
// Quite long
let repr_Fun_of_ST_req__Tbind a b pre (itm : ST.post_t a) post
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
      (requires ST.tree_req f sl0 <==> tree_req (repr_Fun_of_ST f (ST.mk_prog_shape f shp_f) sl0))
      (ensures  req_equiv (ST.Tbind a b pre itm post f g)
                          (ST.mk_prog_shape _ (Sbind _ _ _ shp_f shp_g)) sl0)
  =
    let t = ST.Tbind a b pre itm post f g                                       in
    let s = ST.mk_prog_shape t (Sbind (L.length pre) itm_n post_n shp_f shp_g)  in
    let s_f = ST.mk_prog_shape f shp_f                                          in
    let s_g (x : a) = ST.mk_prog_shape (g x) shp_g                              in
    let r_f = repr_Fun_of_ST f s_f sl0                                          in
    let r_g (x : a) (sl1 : Fl.flist (itm x)) = repr_Fun_of_ST (g x) (s_g x) sl1 in
    let itm' = post_Fun_of_ST itm s_f.shp                                       in

    assert (req_equiv t s sl0 == (
      (ST.tree_req f sl0 /\
      (forall (x : a) (sl1 : Fl.flist (itm x)) .
        ST.tree_ens f sl0 x sl1 ==> ST.tree_req (g x) sl1))
    <==>
      (tree_req r_f /\
      (forall (x : a) (sl1' : post_v itm' x) .
        tree_ens r_f x sl1' ==>
      (let sl1 = sel_ST_of_Fun f s_f sl0 x sl1' in
        tree_req (r_g x sl1) /\
      (forall (y : b) (sl2' : post_v (post_Fun_of_ST post #(L.length (itm x)) shp_g) y) .
        tree_ens (r_g x sl1) y sl2' ==> True))))
    )) by T.(trefl ());

    introduce forall (x : a) . ST.tree_req f sl0 ==> (
      (forall (sl1 : Fl.flist (itm x)) . ST.tree_ens f sl0 x sl1 ==> ST.tree_req (g x) sl1) <==>
      (forall (sl1' : post_v itm' x) .
        tree_ens r_f x sl1' ==>
        tree_req (r_g x (sel_ST_of_Fun f s_f sl0 x sl1'))))
      with introduce _ ==> _
      with _ . begin
        introduce forall (sl1 : Fl.flist (itm x)) . ens_equiv f s_f sl0 x sl1
          with ens_eq_f x sl1;
        FStar.Classical.forall_intro (post_eq_src_iff (post_src_of_shape f s_f x) (post_bij s_f.shp) sl0);
        forall_morph_iff #(post_v itm' x)
          (fun sl1' -> ST.tree_ens f sl0 x (sel_ST_of_Fun f s_f sl0 x sl1') ==>
                    ST.tree_req (g x) (sel_ST_of_Fun f s_f sl0 x sl1'))
          (fun sl1' -> tree_ens r_f x sl1' ==>
                    tree_req (r_g x (sel_ST_of_Fun f s_f sl0 x sl1')))
          (fun sl1' -> ens_equiv_rev f s_f sl0 x sl1';
                    req_eq_g x (sel_ST_of_Fun f s_f sl0 x sl1'))
      end
#pop-options

#push-options "--z3rlimit 60"
let repr_Fun_of_ST_ens__Tbind a b pre (itm : ST.post_t a) post
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
                          (ST.mk_prog_shape _ (Sbind _ _ _ shp_f shp_g)) sl0 y sl2)
  =
    let t = ST.Tbind a b pre itm post f g                                       in
    let s = ST.mk_prog_shape t (Sbind (L.length pre) itm_n post_n shp_f shp_g)  in
    let s_f = ST.mk_prog_shape f shp_f                                          in
    let s_g (x : a) = ST.mk_prog_shape (g x) shp_g                              in
    let r_f = repr_Fun_of_ST f s_f sl0                                          in
    let r_g (x : a) (sl1 : Fl.flist (itm x)) = repr_Fun_of_ST (g x) (s_g x) sl1 in
    let itm'  = post_Fun_of_ST itm s_f.shp                                      in
    let post'g = post_Fun_of_ST post shp_g                                      in
    let post'  = post_Fun_of_ST post s.shp                                      in
    let sl2' : post_v post' y = sel_Fun_of_ST post s.shp y sl2                  in
    let post_src_t = post_src_of_shape t s y                                    in
    let post_src_f (x : a)  = post_src_of_shape f s_f x                         in
    let post_src_g (x : a) = post_src_of_shape (g x) (s_g x) y                  in

    assert (ens_equiv t s sl0 y sl2 ==
      ((exists (x : a) (sl1 : Fl.flist (itm x)) .
         ST.tree_ens f sl0 x sl1 /\ ST.tree_ens (g x) sl1 y sl2)
     <==>
      (post_eq_src post_src_t sl0 sl2 /\
      ((exists (x : a) (sl1' : post_v itm' x) .
         tree_ens r_f x sl1' /\
       (let sl1 = sel_ST_of_Fun f s_f sl0 x sl1' in
        let r_g = r_g x sl1                      in
        (exists (yg : b) (sl2g : post_v (post_Fun_of_ST post #(L.length (itm x)) shp_g) yg) .
         tree_ens r_g yg sl2g /\
        (let sl2f : Fl.flist (post yg) = sel_ST_of_Fun (g x) (s_g x) sl1 yg sl2g in
         tree_ens (Tret b yg post' (Fl.dlist_of_f (sel_Fun_of_ST post s.shp yg sl2f))) y sl2'
         ))))))
    )) by T.(trefl ());

    assert (post_eq_src post_src_t sl0 sl2);

    introduce forall (x : a) .
       (exists (sl1 : Fl.flist (itm x)) . ST.tree_ens f sl0 x sl1 /\ ST.tree_ens (g x) sl1 y sl2)
    <==> (exists (sl1' : post_v itm' x) .
         tree_ens r_f x sl1' /\
       (let sl1 = sel_ST_of_Fun f s_f sl0 x sl1' in
        let r_g = r_g x sl1 in
        (exists (sl2g : post_v post'g y) .
         tree_ens r_g y sl2g /\
         sl2' == sel_Fun_of_ST post s.shp y (sel_ST_of_Fun (g x) (s_g x) sl1 y sl2g)
         )))
    with begin
      introduce forall (sl2g : post_v post'g y) (sl1 : Fl.flist (itm x)) .
        sl2' == sel_Fun_of_ST post s.shp y (sel_ST_of_Fun (g x) (s_g x) sl1 y sl2g)
        <==> (sl2g == sel_Fun_of_ST post shp_g y sl2 /\
           post_eq_src (post_src_g x) sl1 sl2)
      with begin
        let sl2gST = sel_ST_of_Fun (g x) (s_g x) sl1 y sl2g in
        // [sel_Fun_of_ST post s y] is injective (for s = [Sbind _]), the inverse is sel_ST_of_Fun
        U.assert_by (sel_Fun_of_ST post s.shp y sl2 == sel_Fun_of_ST post s.shp y sl2gST
                  ==> sl2 == sl2gST)
          (fun () -> post_eq_src_ST_Fun_ST post_src_t (post_bij s.shp) sl0 sl2;
                  post_eq_src_ST_Fun_ST post_src_t (post_bij s.shp) sl0 sl2gST);
        sel_Fun_ST_Fun  (g x) (s_g x) sl1 y sl2g;
        post_eq_src_iff (post_src_g x) (post_bij shp_g) sl1 sl2
      end;

      FStar.Classical.forall_intro (ens_eq_f x);
      FStar.Classical.forall_intro (post_eq_src_iff (post_src_f x) (post_bij shp_f) sl0);

      exists_morph_iff #(post_v itm' x)
        (fun sl1' -> ST.tree_ens f sl0 x (sel_ST_of_Fun f s_f sl0 x sl1') /\
                  ST.tree_ens (g x) (sel_ST_of_Fun f s_f sl0 x sl1') y sl2)
        (fun sl1' -> tree_ens r_f x sl1' /\
                 (let sl1 = sel_ST_of_Fun f s_f sl0 x sl1' in
                  let r_g = r_g x sl1                      in
                  post_eq_src (post_src_g x) sl1 sl2 /\
                  tree_ens r_g y (sel_Fun_of_ST post shp_g y sl2)))
        (fun sl1' ->
          let sl1 = sel_ST_of_Fun f s_f sl0 x sl1' in
          ens_eq_f x sl1;
          ens_equiv_rev f s_f sl0 x sl1';
          FStar.Classical.move_requires (ens_eq_g x) sl1)
    end
#pop-options

let repr_Fun_of_ST_ens__TbindP a b pre post
      wp f (g : a -> ST.prog_tree b pre post)
      (post_n : nat {ST.post_has_len post post_n})
      (shp_g : ST.shape_tree _ post_n {forall (x : a) . ST.prog_has_shape (g x) shp_g})
      sl0 y sl1
      (ens_eq_g : (x : a) ->
                  Lemma (ens_equiv (g x) (ST.mk_prog_shape (g x) shp_g) sl0 y sl1))
  : Lemma
      (ensures ens_equiv (ST.TbindP a b pre post wp f g)
                         (ST.mk_prog_shape _ (SbindP _ _ shp_g)) sl0 y sl1)
  =
    let t = ST.TbindP a b pre post wp f g                           in
    let s = ST.mk_prog_shape t (SbindP (L.length pre) post_n shp_g) in
    let s_g (x : a) = ST.mk_prog_shape (g x) shp_g                  in
    let r_g (x : a) = repr_Fun_of_ST (g x) (s_g x) sl0              in
    let post'g = post_Fun_of_ST post shp_g                          in
    let post'  = post_Fun_of_ST post s.shp                          in
    let sl1' : post_v post' y = sel_Fun_of_ST post s.shp y sl1      in
    let post_src_t = post_src_of_shape t s y                        in
    let post_src_g (x : a) = post_src_of_shape (g x) (s_g x) y      in


    assert (ens_equiv t s sl0 y sl1 == (
      ((exists (x : a) .
        as_ensures wp x /\ ST.tree_ens (g x) sl0 y sl1)
     <==>
      (post_eq_src post_src_t sl0 sl1 /\
      (exists (x : a) .
       as_ensures wp x /\
      (exists (yg : b) (sl1g : post_v (post_Fun_of_ST post #(L.length #Type pre) shp_g) yg) .
       tree_ens (r_g x) yg sl1g /\
      (let sl1f = sel_ST_of_Fun (g x) (s_g x) sl0 yg sl1g in
       y == yg /\ sl1' == Fl.flist_of_d (Fl.dlist_of_f (sel_Fun_of_ST post s.shp yg sl1f))
      )))))
    )) by T.(trefl ());

    assert (post_eq_src post_src_t sl0 sl1);
  
    introduce forall (x : a {as_ensures wp x}) .
      (ST.tree_ens (g x) sl0 y sl1 <==>
      (exists (sl1g : post_v post'g y) .
         tree_ens (r_g x) y sl1g /\
         sl1' == sel_Fun_of_ST post s.shp y (sel_ST_of_Fun (g x) (s_g x) sl0 y sl1g)))
    with begin
      introduce forall (sl1g : post_v post'g y) .
        sl1' == sel_Fun_of_ST post s.shp y (sel_ST_of_Fun (g x) (s_g x) sl0 y sl1g)
        <==> (sl1g == sel_Fun_of_ST post shp_g y sl1 /\
            post_eq_src (post_src_g x) sl0 sl1)
       with begin
        let sl1gST = sel_ST_of_Fun (g x) (s_g x) sl0 y sl1g in
         U.assert_by (sel_Fun_of_ST post s.shp y sl1 == sel_Fun_of_ST post s.shp y sl1gST
                   ==> sl1 == sl1gST)
          (fun () -> post_eq_src_ST_Fun_ST post_src_t (post_bij s.shp) sl0 sl1;
                  post_eq_src_ST_Fun_ST post_src_t (post_bij s.shp) sl0 sl1gST);
        sel_Fun_ST_Fun (g x) (s_g x) sl0 y sl1g;
        post_eq_src_iff (post_src_g x) (post_bij shp_g) sl0 sl1
       end;
       ens_eq_g x
    end



#push-options "--z3rlimit 10"
let rec repr_Fun_of_ST_req
  (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
  (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
  (sl0 : Fl.flist pre)
  : Lemma (ensures req_equiv t s sl0) (decreases t)
  = ST.match_prog_tree t
    (fun a pre post t -> (s : ST.prog_shape t) -> (sl0 : Fl.flist pre) ->
       squash (ST.tree_req t sl0 <==> tree_req (repr_Fun_of_ST t s sl0)))
    (fun (*ST.Tequiv*) pre post0 p -> fun s sl0 -> ())
    begin fun (*ST.Tframe*) a pre post frame f -> fun s sl0 ->
      let Sframe pre_n post_n frame_n shp_f = s.shp in 
      let sl0' : Fl.flist pre = (Fl.splitAt_ty pre frame sl0)._1 in
      repr_Fun_of_ST_req f (ST.mk_prog_shape f shp_f) sl0'
    end
    (fun (*ST.Tspec*) a pre post req ens -> fun s sl0 -> ())
    (fun (*ST.Tret*) a x post -> fun s sl0 -> ())
    begin fun (*ST.Tbind*) a b pre itm post f g -> fun s sl0 ->
      let Sbind _ itm_n post_n shp_f shp_g = s.shp   in
      let s_f = ST.mk_prog_shape f shp_f             in
      let s_g (x : a) = ST.mk_prog_shape (g x) shp_g in
      repr_Fun_of_ST_req f s_f sl0;
      repr_Fun_of_ST_req__Tbind a b pre itm post f g itm_n post_n shp_f shp_g sl0
        (fun x sl1 -> repr_Fun_of_ST_req (g x) (s_g x) sl1)
        (fun x sl1 -> repr_Fun_of_ST_ens f s_f sl0 x sl1)
    end
    begin fun (*ST.TbindP*) a b pre post wp f g -> fun s sl0 ->
      let SbindP _ post_n shp_g = s.shp              in
      let s_g (x : a) = ST.mk_prog_shape (g x) shp_g in
      let pt0 x = ST.tree_req (g x) sl0              in
      let pt1 x = tree_req (repr_Fun_of_ST (g x) (s_g x) sl0) /\
                    (forall (y : b) (sl1' : post_v (post_Fun_of_ST post #(L.length #Type pre) shp_g) y) .
                    tree_ens (repr_Fun_of_ST (g x) (s_g x) sl0) y sl1' ==> True) in
      calc (<==>) {
        ST.tree_req (ST.TbindP a b pre post wp f g) sl0;
      <==> { _ by T.(apply_lemma (`U.iff_refl); trefl ()) }
        wp (fun x -> ST.tree_req (g x) sl0) /\ True;
      <==> {}
        wp pt0;
      <==> { wp_morph_iff wp pt0 pt1 (fun x -> repr_Fun_of_ST_req (g x) (s_g x) sl0) }
        wp pt1;
      <==> {}
        wp (fun x -> tree_req (repr_Fun_of_ST (g x) (ST.mk_prog_shape (g x) shp_g) sl0) /\
                (forall (y : b) (sl1' : post_v (post_Fun_of_ST post #(L.length #Type pre) shp_g) y) .
                tree_ens (repr_Fun_of_ST (g x) (ST.mk_prog_shape (g x) shp_g) sl0) y sl1' ==> True)) /\ True;
      <==> { _ by T.(apply_lemma (`U.iff_refl); trefl ())}
        tree_req (repr_Fun_of_ST (ST.TbindP a b pre post wp f g)
                                 (ST.mk_prog_shape _ (SbindP _ _ shp_g)) sl0);
      }
    end s sl0

and repr_Fun_of_ST_ens
  (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
  (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
  (sl0 : Fl.flist pre) (res : a) (sl1 : Fl.flist (post res))
  : Lemma (ensures ens_equiv t s sl0 res sl1)
          (decreases t)
  = ST.match_prog_tree t
    (fun a pre post t -> (s : ST.prog_shape t) ->
       (sl0 : Fl.flist pre) -> (res : a) -> (sl1 : Fl.flist (post res)) ->
       squash (ens_equiv t s sl0 res sl1))
    begin fun (*ST.Tequiv*) pre post0 p -> fun s sl0 U.Unit' sl1 ->
      introduce (forall (i : Fin.fin (L.length post0)) . sl1 i === sl0 (p i)) ==>
                sl1 == Fl.apply_perm_r p sl0
        with _ . Fl.flist_extensionality sl1 (Fl.apply_perm_r p sl0) (fun _ -> ());
      Fl.nil_uniq (sel_Fun_of_ST (const_post post0) s.shp U.Unit' sl1);
      Fl.nil_uniq (Fl.flist_of_d Dl.DNil)
    end
    begin fun (*ST.Tframe*) a pre post frame f -> fun s sl0 x sl1 ->
      let Sframe pre_n post_n frame_n shp_f = s.shp in 
      repr_Fun_of_ST_ens__Tframe a pre post frame f post_n shp_f sl0 x sl1
        (fun sl0' sl1' -> repr_Fun_of_ST_ens f (ST.mk_prog_shape f shp_f) sl0' x sl1')
    end
    begin fun (*ST.Tspec*) a pre post req ens -> fun s sl0 x sl1 ->
      let Sspec pre_n post_n = s.shp in
      post_Fun_of_ST__spec post pre_n post_n;
      Fl.flist_extensionality (sel_Fun_of_ST post s.shp x sl1) sl1 (fun _ -> ())
    end
    begin fun (*ST.Tret*) a x post -> fun s sl0 x sl1 ->
      let Sret post_n = s.shp in
      post_Fun_of_ST__ret post post_n;
      Fl.flist_extensionality (sel_Fun_of_ST post s.shp x sl1) sl1 (fun _ -> ())
    end
    begin fun (*ST.Tbind*) a b pre itm post f g -> fun s sl0 y sl2 ->
      let Sbind _ itm_n post_n shp_f shp_g = s.shp   in
      let s_f = ST.mk_prog_shape f shp_f             in
      let s_g (x : a) = ST.mk_prog_shape (g x) shp_g in
      repr_Fun_of_ST_ens__Tbind a b pre itm post f g itm_n post_n shp_f shp_g sl0 y sl2
        (fun x sl1 -> repr_Fun_of_ST_ens f s_f sl0 x sl1)
        (fun x sl1 -> repr_Fun_of_ST_ens (g x) (s_g x) sl1 y sl2)
    end
    begin fun (*ST.TbindP*) a b pre post wp f g -> fun s sl0 y sl1 ->
      let SbindP _ post_n shp_g = s.shp              in
      let s_g (x : a) = ST.mk_prog_shape (g x) shp_g in
      repr_Fun_of_ST_ens__TbindP a b pre post wp f g post_n shp_g sl0 y sl1
        (fun x -> repr_Fun_of_ST_ens (g x) (s_g x) sl0 y sl1)
    end s sl0 res sl1
#pop-options

#pop-options

(*** Steel.Repr.Fun --> Repr.Fun *)

let __begin_repr_fun_of_steel = ()

module Fun = Experiment.Repr.Fun

#push-options "--z3rlimit 40 --ifuel 1 --fuel 1"
let rec repr_Fun_of_Steel_req #val_t #sel_t (t : prog_tree val_t sel_t)
  : Lemma (ensures tree_req t <==> Fun.tree_req (repr_Fun_of_Steel t))
          (decreases t)
  = match t with
  | Tspec a post req ens -> ()
  | Tret a x post sl -> ()
  | Tbind a b itm post f g ->
          repr_Fun_of_Steel_req f;
          introduce forall (x : a) (sl1 : post_v itm x) .
                    (tree_ens f x sl1   <==> Fun.tree_ens (repr_Fun_of_Steel f) ({val_v=x; sel_v=sl1})) /\
                    (tree_req (g x sl1) <==> Fun.tree_req (repr_Fun_of_Steel (g x sl1)))
            with (repr_Fun_of_Steel_ens f x sl1; repr_Fun_of_Steel_req (g x sl1))
  | TbindP a b post wp f g ->
          calc (<==>) {
            tree_req (TbindP a b post wp f g);
          <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
            wp (fun x -> tree_req (g x)) /\ True;
          <==> {wp_morph_iff wp (fun x -> tree_req (g x)) (fun x -> Fun.tree_req (repr_Fun_of_Steel (g x)))
                              (fun x -> repr_Fun_of_Steel_req (g x))}
            wp (fun x -> Fun.tree_req (repr_Fun_of_Steel (g x)));
          <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
            Fun.tree_req (repr_Fun_of_Steel (TbindP a b post wp f g));
          }

and repr_Fun_of_Steel_ens #val_t #sel_t (t : prog_tree val_t sel_t)
                          (val_v : val_t) (sel_v : Fl.flist (sel_t val_v))
  : Lemma (ensures tree_ens t val_v sel_v <==> Fun.tree_ens (repr_Fun_of_Steel t) ({val_v; sel_v}))
          (decreases t)
  = match t with
  | Tspec a post req ens ->
          assert (tree_ens (Tspec a post req ens) val_v sel_v == ens val_v sel_v)
               by T.(trefl ());
          assert (Fun.tree_ens (repr_Fun_of_Steel (Tspec a post req ens)) ({val_v; sel_v})
               == sl_uncurrify ens ({val_v; sel_v}))
               by T.(trefl ())
  | Tret a x post sl -> ()
  | Tbind a b itm post f g ->
          assert (tree_ens (Tbind a b itm post f g) val_v sel_v
               == (exists (x : a) (sl1 : post_v itm x) . tree_ens f x sl1 /\ tree_ens (g x sl1) val_v sel_v) )
               by T.(trefl ());
          assert (Fun.tree_ens (repr_Fun_of_Steel (Tbind a b itm post f g)) ({val_v; sel_v})
               == (let () = U.block_red in
                   sl_tys.ex ({val_t=a; sel_t=itm}) (fun (x_sl1 : sl_tys_v ({val_t=a; sel_t=itm})) ->
                     Fun.tree_ens (repr_Fun_of_Steel f) x_sl1 /\
                     Fun.tree_ens
                      (sl_uncurrify (fun x sls -> repr_Fun_of_Steel (g x sls)) x_sl1) ({val_v; sel_v}))))
               by T.(norm [delta_only [`%repr_Fun_of_Steel; `%Fun.tree_ens]; zeta];
                     norm [delta_only [`%U.block_red]; iota];
                     trefl ());
          introduce forall (x : a) (sl1 : post_v itm x) .
                    (tree_ens f x sl1   <==> Fun.tree_ens (repr_Fun_of_Steel f) ({val_v=x; sel_v=sl1})) /\
                    (tree_ens (g x sl1) val_v sel_v <==> Fun.tree_ens (repr_Fun_of_Steel (g x sl1)) ({val_v; sel_v}))
            with (repr_Fun_of_Steel_ens f x sl1; repr_Fun_of_Steel_ens (g x sl1) val_v sel_v)
  | TbindP a b post wp f g ->
          assert (tree_ens (TbindP a b post wp f g) val_v sel_v
              == (exists (x : a) . as_ensures wp x /\ tree_ens (g x) val_v sel_v))
            by T.(trefl ());
          assert (Fun.tree_ens (repr_Fun_of_Steel (TbindP a b post wp f g)) ({val_v; sel_v})
              == (exists (x : a) . as_ensures wp x /\ Fun.tree_ens (repr_Fun_of_Steel (g x)) ({val_v; sel_v})))
            by T.(trefl ());
          introduce forall (x : a) .
                    (tree_ens (g x) val_v sel_v <==> Fun.tree_ens (repr_Fun_of_Steel (g x)) ({val_v; sel_v}))
            with repr_Fun_of_Steel_ens (g x) val_v sel_v
#pop-options
