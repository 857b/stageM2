module Experiment.Steel.Repr.M

module T = FStar.Tactics
module L = FStar.List.Pure


#set-options "--ide_id_info_off"

(***** [vprop_list] *)

let rec vprop_of_list_can_be_split (vs : vprop_list) (i : nat {i < L.length vs})
  : Lemma (ensures can_be_split (vprop_of_list vs) (VUnit (L.index vs i))) (decreases vs)
  = let v :: vs = vs in
    if i = 0
    then can_be_split_star_l (VUnit v) (vprop_of_list vs)
    else begin
      can_be_split_star_r (VUnit v) (vprop_of_list vs);
      vprop_of_list_can_be_split vs (i-1);
      can_be_split_trans (VUnit v `star` vprop_of_list vs) (vprop_of_list vs) (VUnit (L.index vs (i-1)))
    end

let rec flatten_vprop_aux_eq (vp : vprop) (acc : vprop_list)
  : Lemma (ensures flatten_vprop_aux vp acc == L.(flatten_vprop vp @ acc)) (decreases vp)
  = match vp with
  | VUnit _ -> ()
  | VStar vp0 vp1 ->
          calc (==) {
            flatten_vprop_aux (VStar vp0 vp1) acc;
          == {}
            flatten_vprop_aux vp0 (flatten_vprop_aux vp1 acc);
          == {flatten_vprop_aux_eq vp0 (flatten_vprop_aux vp1 acc);
              flatten_vprop_aux_eq vp1 acc}
            L.(flatten_vprop vp0 @ (flatten_vprop vp1 @ acc));
          == {L.append_assoc (flatten_vprop vp0) (flatten_vprop vp1) acc}
            L.((flatten_vprop vp0 @ (flatten_vprop vp1 @ [])) @ acc);
          == {flatten_vprop_aux_eq vp1 [];
              flatten_vprop_aux_eq vp0 (flatten_vprop_aux vp1 [])}
            L.(flatten_vprop_aux (VStar vp0 vp1) [] @ acc);
          }

let flatten_vprop_VStar (vp0 vp1 : vprop)
  =
    flatten_vprop_aux_eq vp0 (flatten_vprop_aux vp1 []);
    flatten_vprop_aux_eq vp1 []

let rec vprop_of_list_append (vs0 vs1 : vprop_list)
  : Lemma (ensures equiv (vprop_of_list L.(vs0@vs1)) (vprop_of_list vs0 `star` vprop_of_list vs1))
          (decreases vs0)
  = match vs0 with
  | []     -> assert (equiv (vprop_of_list vs1) (emp `star` vprop_of_list vs1))
                by (init_resolve_tac ())
  | v :: vs -> let v0 = VUnit v in
             let vl0 = vprop_of_list vs in
             let vl1 = vprop_of_list vs1 in
             let vl2 = vprop_of_list L.(vs @ vs1) in
             assert_norm (vprop_of_list L.((v :: vs) @ vs1) == v0 `star` vl2);
             equiv_refl v0;
             vprop_of_list_append vs vs1;
             star_congruence v0       vl2
                             v0 (vl0 `star` vl1);
             star_associative v0 vl0 vl1;
             equiv_sym ((v0 `star` vl0) `star` vl1) (v0 `star` (vl0 `star` vl1));
             
             equiv_trans (v0 `star` vl2)
                         (v0 `star` (vl0 `star` vl1))
                         ((v0 `star` vl0) `star` vl1);
             assert_norm (vprop_of_list (v :: vs) `star` vprop_of_list vs1
                      == (v0 `star` vl0) `star` vl1)

let rec vprop_equiv_flat (vp : vprop)
  : Lemma (ensures equiv (vprop_of_list (flatten_vprop vp)) vp) (decreases vp)
  = match vp with
  | VUnit v     -> assert (equiv (VUnit v `star` emp) (VUnit v))
                      by (init_resolve_tac ())
  | VStar v0 v1 -> flatten_vprop_VStar v0 v1;
                  vprop_of_list_append (flatten_vprop v0) (flatten_vprop v1);
                  vprop_equiv_flat v0;
                  vprop_equiv_flat v1;
                  star_congruence (vprop_of_list (flatten_vprop v0)) (vprop_of_list (flatten_vprop v1)) v0 v1;
                  equiv_trans (vprop_of_list L.(flatten_vprop v0 @ flatten_vprop v1))
                              (vprop_of_list (flatten_vprop v0) `star` vprop_of_list (flatten_vprop v1))
                              (v0 `star` v1)


let rec steel_elim_vprop_of_list_append #opened (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list L.(vs0@vs1)) (fun () -> vprop_of_list vs0 `star` vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> split_vars_list vs0 vs1 (rmem_sl_list (vs0@vs1) h0)
                        == (rmem_sl_list vs0 h1, rmem_sl_list vs1 h1))
      (decreases %[vs0; 0])
  =
    match vs0 with
    | [] -> change_equal_slprop (vprop_of_list L.(vs0@vs1)) (vprop_of_list vs1);
           change_equal_slprop emp (vprop_of_list vs0)
    | v0 :: vs0' -> steel_elim_vprop_of_list_append__cons vs0 vs1 v0 vs0'

and steel_elim_vprop_of_list_append__cons #opened (vs0 vs1 : vprop_list) v0 (vs0' : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list L.(vs0@vs1)) (fun () -> vprop_of_list vs0 `star` vprop_of_list vs1)
      (requires fun _ -> vs0 == v0 :: vs0')
      (ensures fun h0 () h1 -> split_vars_list vs0 vs1 (rmem_sl_list (vs0@vs1) h0)
                        == (rmem_sl_list vs0 h1, rmem_sl_list vs1 h1))
      (decreases %[vs0'; 1])
  =
    change_equal_slprop (vprop_of_list L.(vs0@vs1)) (VUnit v0 `star` vprop_of_list L.(vs0'@vs1));
    (**) let sl_v0 : Ghost.erased (t_of (VUnit v0)) = gget (VUnit v0) in
    (**) let sl_vs01 : Ghost.erased (t_of (vprop_of_list L.(vs0'@vs1))) = gget (vprop_of_list L.(vs0'@vs1)) in
    steel_elim_vprop_of_list_append vs0' vs1;
    (**) let sl_vs0  = gget (vprop_of_list vs0') in
    (**) let sl_vs1  = gget (vprop_of_list vs1) in
    change_equal_slprop (VUnit v0 `star` vprop_of_list vs0') (vprop_of_list (vs0));
    calc (==) {
      split_vars_list (v0 :: vs0') vs1 (vpl_sels L.(v0 :: vs0' @ vs1) (Ghost.reveal sl_v0, Ghost.reveal sl_vs01));
    == {split_vars__cons v0 vs0' vs1 sl_v0 (vpl_sels L.(vs0' @ vs1) sl_vs01)}
      (let xs0, xs1 = split_vars_list vs0' vs1 (vpl_sels L.(vs0' @ vs1) sl_vs01) in
       Dl.DCons v0.t sl_v0 _ xs0, xs1);
    == {}
      Dl.DCons v0.t sl_v0 _ (vpl_sels vs0' sl_vs0), vpl_sels vs1 sl_vs1;
    }

let steel_elim_vprop_of_list_append_f #opened (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list L.(vs0@vs1)) (fun () -> vprop_of_list vs0 `star` vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> split_vars vs0 vs1 (rmem_sels (vs0@vs1) h0)
                        == (rmem_sels vs0 h1, rmem_sels vs1 h1))
  =
    let sl = gget (vprop_of_list L.(vs0@vs1)) in
    Ll.map_append Mkvprop'?.t vs0 vs1;
    (* TODO: Why is this necessary ? *)
    assert (vprop_list_sels_t L.(vs0 @ vs1) == L.(vprop_list_sels_t vs0 @ vprop_list_sels_t vs1))
        by T.(norm [delta_only [`%vprop_list_sels_t]]; smt ());
    Fl.splitAt_ty_of_d (vprop_list_sels_t vs0) (vprop_list_sels_t vs1) (vpl_sels L.(vs0 @ vs1) sl);
    steel_elim_vprop_of_list_append vs0 vs1


let rec steel_intro_vprop_of_list_append #opened (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list vs0 `star` vprop_of_list vs1) (fun () -> vprop_of_list L.(vs0@vs1))
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> split_vars_list vs0 vs1 (rmem_sl_list (vs0@vs1) h1)
                        == (rmem_sl_list vs0 h0, rmem_sl_list vs1 h0))
      (decreases vs0)
  = match vs0 with
    | [] -> change_equal_slprop (vprop_of_list vs0) emp;
           change_equal_slprop (vprop_of_list vs1) (vprop_of_list L.(vs0@vs1))
    | v0 :: vs0' ->
           change_equal_slprop (vprop_of_list (vs0)) (VUnit v0 `star` vprop_of_list vs0');
           (**) let sl_v0   = gget (VUnit v0) in
           steel_intro_vprop_of_list_append vs0' vs1;
           (**) let sl_vs01 = gget (vprop_of_list L.(vs0'@vs1)) in
           (**) split_vars__cons v0 vs0' vs1 sl_v0 (vpl_sels L.(vs0' @ vs1) sl_vs01);
           change_equal_slprop (VUnit v0 `star` vprop_of_list L.(vs0'@vs1)) (vprop_of_list L.(vs0@vs1))

let steel_intro_vprop_of_list_append_f #opened (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list vs0 `star` vprop_of_list vs1) (fun () -> vprop_of_list L.(vs0@vs1))
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> split_vars vs0 vs1 (rmem_sels (vs0@vs1) h1)
                        == (rmem_sels vs0 h0, rmem_sels vs1 h0))
  =
    steel_intro_vprop_of_list_append vs0 vs1;
    let sl = gget (vprop_of_list L.(vs0@vs1)) in
    Ll.map_append Mkvprop'?.t vs0 vs1;
    assert (vprop_list_sels_t L.(vs0 @ vs1) == L.(vprop_list_sels_t vs0 @ vprop_list_sels_t vs1))
        by T.(norm [delta_only [`%vprop_list_sels_t]]; smt ());
    Fl.splitAt_ty_of_d (vprop_list_sels_t vs0) (vprop_list_sels_t vs1) (vpl_sels L.(vs0 @ vs1) sl)


(***** applying a permutation on the context's vprop *)

let rec steel_change_swap (#opened:Mem.inames)
          (vs0 : vprop_list) (i : nat {i <= L.length vs0 - 2})
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list (Perm.list_swap i vs0))
      (requires fun _ -> True) (ensures fun h0 () h1 ->
        rmem_sl_list (Perm.list_swap i vs0) h1 === Dl.dlist_swap i (rmem_sl_list vs0 h0))
      (decreases i)
  = if i = 0
    then begin
      let v0 :: v1 :: vs = vs0 in
      change_equal_slprop (vprop_of_list vs0)
                          (VUnit v0 `star` (VUnit v1 `star` vprop_of_list vs));
      change_equal_slprop (VUnit v1 `star` (VUnit v0 `star` vprop_of_list vs))
                          (vprop_of_list (Perm.list_swap i vs0))
    end else begin
      let v0 :: vs = vs0 in
      change_equal_slprop (vprop_of_list vs0)
                          (VUnit v0 `star` vprop_of_list vs);
      steel_change_swap vs (i-1);
      change_equal_slprop (VUnit v0 `star` vprop_of_list (Perm.list_swap (i-1) vs))
                          (vprop_of_list (Perm.list_swap i vs0))
    end

let rec steel_change_vequiv_aux (#opened:Mem.inames)
          (n : nat) (vs0 vs1 : (l:vprop_list{L.length l == n}))
          (fs : list (i:nat{i <= n-2}))
          (eqv : squash (vs1 == Perm.apply_perm_r (Perm.comp_list (L.map (Perm.perm_f_swap #n) fs)) vs0))
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list vs1)
      (requires fun _ -> True) (ensures fun h0 () h1 ->
        rmem_sl_list vs1 h1 == Dl.apply_pequiv (vequiv_sl (Perm.comp_list (L.map Perm.perm_f_swap fs)))
                                            (rmem_sl_list vs0 h0))
      (decreases fs)
  =
  let sl0  = gget (vprop_of_list vs0) in
  match fs with
  | []       -> change_equal_slprop (vprop_of_list vs0) (vprop_of_list vs1)
  | f0 :: fs' -> let pfs = Perm.comp_list (L.map (Perm.perm_f_swap #n) fs') in
               let vs' = Perm.apply_perm_r pfs vs0 in
               steel_change_vequiv_aux n vs0 vs' fs' ();
               let sl1' : sl_list vs' =
                 Dl.apply_pequiv #(vprop_list_sels_t vs0) #(vprop_list_sels_t vs')
                                  (vequiv_sl (U.cast (Perm.perm_f (L.length vs0)) pfs))
                                  (vpl_sels vs0 sl0) in
               steel_change_swap vs' f0;
               Perm.apply_swap_as_rec n f0 vs';
               Perm.apply_r_comp (Perm.perm_f_swap #n f0) pfs vs0;
               change_equal_slprop (vprop_of_list (Perm.list_swap f0 vs'))
                                   (vprop_of_list vs1);
               let sl1 = gget (vprop_of_list vs1) in
               assert (vpl_sels vs1 sl1 === Dl.dlist_swap f0 sl1');
               Dl.apply_swap_as_rec n f0 sl1';
               Dl.apply_r_comp (Perm.perm_f_swap #n f0) pfs (vpl_sels vs0 sl0)

let steel_change_vequiv (#vs0 #vs1 : vprop_list) (#opened:Mem.inames) (f : vequiv vs0 vs1)
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> rmem_sels vs1 h1 == extract_vars f (rmem_sels vs0 h0))
  =
    let sl0 = gget (vprop_of_list vs0) in
    Fl.apply_perm_r_of_d f (vpl_sels vs0 sl0);
    steel_change_vequiv_aux (L.length vs0) vs0 vs1 (Perm.perm_f_to_swap f) ()


inline_for_extraction
let repr_steel_subcomp
      (#a : Type) (#pre : pre_t) (#post : post_t a)
      (req_f : req_t pre) (ens_f : ens_t pre a post)
      (req_g : req_t pre) (ens_g : ens_t pre a post)
      (pf_req : (sl0 : sl_t pre) ->
                Lemma (requires req_g sl0) (ensures req_f sl0))
      (pf_ens : (sl0 : sl_t pre) -> (x : a) -> (sl1 : sl_t (post x)) ->
                Lemma (requires req_f sl0 /\ req_g sl0 /\ ens_f sl0 x sl1) (ensures ens_g sl0 x sl1))
      (r : repr_steel_t a pre post req_f ens_f)
  : repr_steel_t a pre post req_g ens_g
  = 
    (fun () ->
      (**) let sl0 = gget (vprop_of_list pre) in
      (**) pf_req (vpl_sels_f pre sl0);
      let x = r () in
      (**) let sl1 = gget (vprop_of_list (post x)) in
      (**) pf_ens (vpl_sels_f pre sl0) x (vpl_sels_f (post x) sl1);
      Steel.Effect.Atomic.return x)


(***** Monad combiners *)  

inline_for_extraction
let repr_of_steel_steel
      (a : Type) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
      (pre' : pre_t) (post' : post_t a) (frame : vprop_list)
      (p0 : vequiv pre' L.(pre @ frame)) (p1 : ((x : a) -> vequiv (post x @ frame) (post' x)))
      ($f : repr_steel_t a pre post req ens)
  : (let c = TCspec #a #pre #post #req #ens pre' post' frame p0 p1 in
     repr_steel_t a pre' post' (tree_req _ c) (tree_ens _ c))
  = fun () ->
    (**) steel_change_vequiv p0;
    (**) steel_elim_vprop_of_list_append_f pre frame;
    let x = f () in
    (**) steel_intro_vprop_of_list_append_f (post x) frame;
    (**) let sl1' = gget (vprop_of_list L.(post x @ frame)) in
    (**) steel_change_vequiv (p1 x);
    (**) let sl1'' = gget (vprop_of_list (post' x)) in
    (**) assert (vpl_sels_f (post' x) sl1''
    (**)      == extract_vars (p1 x) (vpl_sels_f L.(post x @ frame) sl1'));
    (**) extract_vars_sym_l (p1 x) (vpl_sels_f L.(post x @ frame) sl1');
    Steel.Effect.Atomic.return x

inline_for_extraction
let return_steel
      (a : Type) (x : a) (sl_hint : post_t a)
      (pre : pre_t) (post : post_t a)
      (p : vequiv pre (post x))
  : (let c = TCret #a #x #sl_hint pre post p in
     repr_steel_t a pre post (tree_req _ c) (tree_ens _ c))
  = fun () ->
    (**) steel_change_vequiv p;
    Steel.Effect.Atomic.return x

let elim_tree_req_bind (#a #b : Type) (f : prog_tree a) (g : a -> prog_tree b)
      (#pre : pre_t) (#post : post_t b) (#itm : post_t a)
      (cf  : tree_cond f pre itm) (cg : (x:a) -> tree_cond (g x) (itm x) post)
      (sl0 : t_of (vprop_of_list pre))
  : Lemma (requires tree_req _ (TCbind #a #b #f #g pre itm post cf cg) (vpl_sels_f pre sl0))
          (ensures  tree_req f cf (vpl_sels_f pre sl0) /\
                    (forall (x : a) (sl1 : t_of (vprop_of_list (itm x))) .
                      tree_ens f cf (vpl_sels_f pre sl0) x (vpl_sels_f (itm x) sl1) ==>
                      tree_req (g x) (cg x) (vpl_sels_f (itm x) sl1)))
  = assert_norm (tree_req _ (TCbind #a #b #f #g pre itm post cf cg) (vpl_sels_f pre sl0) == (
      tree_req f cf (vpl_sels_f pre sl0) /\
      (forall (x : a) (sl1 : sl_t (itm x)) .
         tree_ens f cf (vpl_sels_f pre sl0) x sl1 ==> tree_req (g x) (cg x) sl1)
    ))

let intro_tree_ens_bind (#a #b : Type) (f : prog_tree a) (g : a -> prog_tree b)
      (#pre : pre_t) (#post : post_t b) (#itm : post_t a)
      (cf  : tree_cond f pre itm) (cg : (x:a) -> tree_cond (g x) (itm x) post)
      (sl0 : t_of (vprop_of_list pre)) (x : a) (sl1 : t_of (vprop_of_list (itm x)))
      (y : b) (sl2 : t_of (vprop_of_list (post y)))
  : Lemma (requires tree_req f cf (vpl_sels_f pre sl0) /\
                    tree_ens f cf (vpl_sels_f pre sl0) x (vpl_sels_f (itm x) sl1) /\
                    tree_ens (g x) (cg x) (vpl_sels_f (itm x) sl1) y (vpl_sels_f (post y) sl2))
          (ensures  tree_ens _ (TCbind #a #b #f #g pre itm post cf cg)
                             (vpl_sels_f pre sl0) y (vpl_sels_f (post y) sl2))
  = assert_norm (tree_ens _ (TCbind #a #b #f #g pre itm post cf cg)
                          (vpl_sels_f pre sl0) y (vpl_sels_f (post y) sl2) == (
        (exists (x : a) (sl1 : sl_t (itm x)) .
          tree_ens f cf (vpl_sels_f pre sl0) x sl1 /\
          tree_ens (g x) (cg x) sl1 y (vpl_sels_f (post y) sl2))
    ))

inline_for_extraction
let bind_steel
      (a : Type) (b : Type) (f : prog_tree a) (g : (a -> prog_tree b))
      (pre : pre_t) (itm : post_t a) (post : post_t b)
      (cf : tree_cond f pre itm) (cg : ((x : a) -> tree_cond (g x) (itm x) post))
      ($rf : repr_steel_t a pre itm (tree_req f cf) (tree_ens f cf))
      ($rg : (x : a) -> repr_steel_t b (itm x) post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbind #a #b #f #g pre itm post cf cg in
     repr_steel_t b pre post (tree_req _ c) (tree_ens _ c))
  = fun () ->
    (**) let sl0 = gget (vprop_of_list pre) in
    (**) elim_tree_req_bind f g cf cg sl0;
    let x = rf () in
    (**) let sl1 = gget (vprop_of_list (itm x)) in
    let y = rg x () in
    (**) let sl2 = gget (vprop_of_list (post y)) in
    (**) intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2;
    Steel.Effect.Atomic.return y
