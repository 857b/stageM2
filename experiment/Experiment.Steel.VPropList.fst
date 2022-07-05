module Experiment.Steel.VPropList

module T  = FStar.Tactics
module L  = FStar.List.Pure
module SH = Experiment.Steel.Steel
module Msk  = Learn.List.Mask


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

let rec flatten_vprop_aux_eq #vp ve acc
  : Lemma (ensures flatten_vprop_aux ve acc == L.(flatten_vprop ve @ acc)) (decreases ve)
  = match ve with
  | VeEmp    -> ()
  | VeUnit _ -> ()
  | VeStar ve0 ve1 ->
          calc (==) {
            flatten_vprop_aux (VeStar ve0 ve1) acc;
          == {}
            flatten_vprop_aux ve0 (flatten_vprop_aux ve1 acc);
          == {flatten_vprop_aux_eq ve0 (flatten_vprop_aux ve1 acc);
              flatten_vprop_aux_eq ve1 acc}
            L.(flatten_vprop ve0 @ (flatten_vprop ve1 @ acc));
          == {L.append_assoc (flatten_vprop ve0) (flatten_vprop ve1) acc}
            L.((flatten_vprop ve0 @ (flatten_vprop ve1 @ [])) @ acc);
          == {flatten_vprop_aux_eq ve1 [];
              flatten_vprop_aux_eq ve0 (flatten_vprop_aux ve1 [])}
            L.(flatten_vprop_aux (VeStar ve0 ve1) [] @ acc);
          }

let flatten_vprop_VStar #vp0 ve0 #vp1 ve1
  =
    flatten_vprop_aux_eq ve0 (flatten_vprop_aux ve1 []);
    flatten_vprop_aux_eq ve1 []

let rec vprop_equiv_flat vp ve
  : Lemma (ensures equiv (vprop_of_list (flatten_vprop ve)) vp) (decreases ve)
  = match ve with
  | VeEmp       -> equiv_refl emp
  | VeUnit v    -> assert (equiv (VUnit v `star` emp) (VUnit v))
                      by (init_resolve_tac ())
  | VeStar #vp0 ve0 #vp1 ve1 ->
           flatten_vprop_VStar ve0 ve1;
           vprop_of_list_append (flatten_vprop ve0) (flatten_vprop ve1);
           vprop_equiv_flat vp0 ve0;
           vprop_equiv_flat vp1 ve1;
           star_congruence (vprop_of_list (flatten_vprop ve0)) (vprop_of_list (flatten_vprop ve1)) vp0 vp1;
           equiv_trans (vprop_of_list L.(flatten_vprop ve0 @ flatten_vprop ve1))
                       (vprop_of_list (flatten_vprop ve0) `star` vprop_of_list (flatten_vprop ve1))
                       (vp0 `star` vp1)


let sel'_sub (#p : vprop) (vs : vprop_list)
             (h : rmem p{can_be_split p (vprop_of_list vs)})
  : sl_t vs
  = sel' vs (focus_rmem h (vprop_of_list vs))


#push-options "--ifuel 1 --fuel 1"
let rec sel_list_eq'_sub (#p : vprop) (vs : vprop_list)
                    (h : rmem p{can_be_split p (vprop_of_list vs)})
  : Lemma (sel_list' #p vs h == Fl.dlist_of_f_g (sel'_sub #p vs h))
  = match vs with
  | [] -> ()
  | v0 :: vs ->
       SH.rmem_star_eq (VUnit v0) (vprop_of_list vs) h;
       calc (==) {
         sel_list' #p (v0 :: vs) h;
       == {}
         Dl.DCons v0.t (h (VUnit v0)) _ (sel_list' #p vs h);
       == { sel_list_eq'_sub #p vs h }
         Dl.DCons v0.t (h (VUnit v0)) _ (Fl.dlist_of_f_g (sel'_sub #p vs h));
       == { Dl.dlist_extensionality
              (Dl.DCons v0.t (h (VUnit v0)) _ (Fl.dlist_of_f_g (sel'_sub #p vs h)))
              (Fl.dlist_of_f_g (sel'_sub #p (v0 :: vs) h))
              (fun i -> vprop_of_list_can_be_split (v0 :: vs) i;
                     SH.focus_rmem_feq p (vprop_of_list (v0 :: vs)) (VUnit (L.index (v0 :: vs) i)) h;
                     if i > 0 then begin
                       vprop_of_list_can_be_split vs (i - 1);
                       SH.focus_rmem_feq p (vprop_of_list vs) (VUnit (L.index vs (i - 1))) h
                     end ) }
         Fl.dlist_of_f_g (sel'_sub #p (v0 :: vs) h);
       }
#pop-options

let sel_list_eq' (vs : vprop_list) (h : rmem (vprop_of_list vs))
  : Lemma (sel_list vs h == Fl.dlist_of_f_g (sel' vs h))
  = sel_list_eq'_sub vs h;
    focus_rmem_refl (vprop_of_list vs) h

let sel_eq' : squash (sel == sel_f')
  = U.funext_eta sel_f' sel (_ by T.(trefl ())) (_ by T.(trefl ())) (fun vs ->
    U.funext_eta_gtot (sel_f' vs) (sel vs) (_ by T.(trefl ())) (_ by T.(trefl ())) (fun h ->
      sel_f_eq' vs h))


let rew_forall_sl_f_app (v0 v1 : vprop_list) (p0 : sl_f L.(v0 @ v1) -> Type) (p1 : Type)
    (_ : squash ((forall (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1)) <==> p1))
  : squash ((forall (sl : sl_f L.(v0 @ v1)) . p0 sl) <==> p1)
  =
    introduce (forall (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1)) ==>
              (forall (sl : sl_f L.(v0 @ v1)) . p0 sl)
      with _ . introduce forall sl . _
      with (let sl0, sl1 = split_vars v0 v1 sl in
            Ll.pat_append ();
            FStar.Classical.forall_intro (Fl.splitAt_ty_append (vprop_list_sels_t v0) (vprop_list_sels_t v1));
            assert (sl == append_vars sl0 sl1);
            eliminate forall (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1) with sl0 sl1);
    introduce (forall (sl : sl_f L.(v0 @ v1)) . p0 sl) ==>
              (forall (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1))
      with _ . introduce forall sl0 sl1 . _
      with eliminate forall (sl : sl_f L.(v0 @ v1)) . p0 sl with (append_vars sl0 sl1)

let rew_exists_sl_f_app (v0 v1 : vprop_list) (p0 : sl_f L.(v0 @ v1) -> Type) (p1 : Type)
    (_ : squash ((exists (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1)) <==> p1))
  : squash ((exists (sl : sl_f L.(v0 @ v1)) . p0 sl) <==> p1)
  =
    introduce (exists (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1)) ==>
              (exists (sl : sl_f L.(v0 @ v1)) . p0 sl)
      with _ . eliminate exists (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1)
      returns _
      with _ . introduce exists (sl : sl_f L.(v0 @ v1)) . p0 sl
        with (append_vars sl0 sl1) and ();
    introduce (exists (sl : sl_f L.(v0 @ v1)) . p0 sl) ==>
              (exists (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1))
      with _ . eliminate exists (sl : sl_f L.(v0 @ v1)) . p0 sl
      returns _
      with _ . (
         let sl0, sl1 = split_vars v0 v1 sl in
         Ll.pat_append ();
         FStar.Classical.forall_intro (Fl.splitAt_ty_append (vprop_list_sels_t v0) (vprop_list_sels_t v1));
         assert (sl == append_vars sl0 sl1);
         introduce exists (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1)
           with sl0 sl1 and ())


#push-options "--ifuel 0 --fuel 0"
let append_vars_mask_index
      (#vs : vprop_list) (m : Msk.mask_t vs)
      (sl0 : sl_f Msk.(filter_mask m vs)) (sl1 : sl_f Msk.(filter_mask (mask_not m) vs))
      (i : Ll.dom vs)
  : Lemma (append_vars_mask m sl0 sl1 i
       == (if L.index m i then U.cast _ (sl0 Msk.(mask_push m i))
                          else U.cast _ (sl1 Msk.(mask_push (mask_not m) i))))
  = Msk.mask_perm_append'_index m i
#pop-options

let append_filter_vars_mask
      (#vs : vprop_list) (m : Msk.mask_t vs) (sl : sl_f vs)
  : Lemma (append_vars_mask m (filter_sl m sl) (filter_sl (Msk.mask_not m) sl) == sl)
  =
    (**) Ll.pat_append ();
    Msk.filter_mask_fl_perm_append' m _ sl

#push-options "--fuel 0 --ifuel 0"
let filter_append_vars_mask
      (#vs : vprop_list) (m : Msk.mask_t vs)
      (sl0 : sl_f Msk.(filter_mask m vs)) (sl1 : sl_f Msk.(filter_mask (mask_not m) vs))
  : Lemma (filter_sl               m  (append_vars_mask m sl0 sl1) == sl0 /\
           filter_sl (Msk.mask_not m) (append_vars_mask m sl0 sl1) == sl1)
  =
    Fl.flist_extensionality (filter_sl               m  (append_vars_mask m sl0 sl1)) sl0
      (fun i -> Msk.mask_perm_append'_index m (Msk.mask_pull m i));
    Fl.flist_extensionality (filter_sl Msk.(mask_not m) (append_vars_mask m sl0 sl1)) sl1
      (fun i -> Msk.mask_perm_append'_index m Msk.(mask_pull (mask_not m) i))
#pop-options


let split_vars__cons (v0 : vprop') (vs0 vs1 : vprop_list) (x0 : v0.t) (xs : sl_list L.(vs0@vs1))
  : Lemma (ensures split_vars_list (v0 :: vs0) vs1 (Dl.DCons v0.t x0 (vprop_list_sels_t L.(vs0@vs1)) xs)
               == (let xs0, xs1 = split_vars_list vs0 vs1 xs in
                   Dl.DCons v0.t x0 (vprop_list_sels_t vs0) xs0, xs1))
  = Ll.map_append Mkvprop'?.t vs0 vs1

let steel_elim_vprop_of_list_cons_f (#opened : Mem.inames) (v : vprop') (vs : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list (v :: vs)) (fun () -> VUnit v `star` vprop_of_list vs)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel_f (v :: vs) h0 == Fl.cons (h1 (VUnit v)) (sel_f vs h1))
  =
    let sl0 = gget_f (v :: vs) in
    change_equal_slprop (vprop_of_list (v :: vs)) (VUnit v `star` vprop_of_list vs);
    let x0  = gget' v in
    let x0  = Ghost.reveal x0 in
    let sl1 = gget_f vs in
    Fl.flist_extensionality sl0 (U.cast _ (Fl.cons x0 sl1)) (fun _ -> ())

let steel_intro_vprop_of_list_cons_f (#opened : Mem.inames) (v : vprop') (vs : vprop_list)
  : SteelGhost unit opened
      (VUnit v `star` vprop_of_list vs) (fun () -> vprop_of_list (v :: vs))
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel_f (v :: vs) h1 == Fl.cons (h0 (VUnit v)) (sel_f vs h0))
  =
    let x0  = gget' v in
    let x0  = Ghost.reveal x0 in
    let sl1 = gget_f vs in
    change_equal_slprop (VUnit v `star` vprop_of_list vs) (vprop_of_list (v :: vs));
    let sl0 = gget_f (v :: vs) in
    Fl.flist_extensionality sl0 (U.cast _ (Fl.cons x0 sl1)) (fun _ -> ())


let rec steel_elim_vprop_of_list_append #opened (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list L.(vs0@vs1)) (fun () -> vprop_of_list vs0 `star` vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> split_vars_list vs0 vs1 (sel_list L.(vs0@vs1) h0)
                        == (sel_list vs0 h1, sel_list vs1 h1))
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
      (ensures fun h0 () h1 -> split_vars_list vs0 vs1 (sel_list L.(vs0@vs1) h0)
                        == (sel_list vs0 h1, sel_list vs1 h1))
      (decreases %[vs0'; 1])
  =
    change_equal_slprop (vprop_of_list L.(vs0@vs1)) (VUnit v0 `star` vprop_of_list L.(vs0'@vs1));
    (**) let sl_v0   : Ghost.erased (v0.t) = gget' v0 in
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
      (ensures fun h0 () h1 -> sel_f L.(vs0@vs1) h0 == append_vars (sel_f vs0 h1) (sel_f vs1 h1))
  =
    let sl = gget (vprop_of_list L.(vs0@vs1)) in
    Ll.map_append Mkvprop'?.t vs0 vs1;
    (* TODO: Why is this necessary ? *)
    assert (vprop_list_sels_t L.(vs0 @ vs1) == L.(vprop_list_sels_t vs0 @ vprop_list_sels_t vs1))
        by T.(norm [delta_only [`%vprop_list_sels_t]]; smt ());
    Fl.splitAt_ty_of_d (vprop_list_sels_t vs0) (vprop_list_sels_t vs1) (vpl_sels L.(vs0 @ vs1) sl);
    steel_elim_vprop_of_list_append vs0 vs1;
    Fl.splitAt_ty_append (vprop_list_sels_t vs0) (vprop_list_sels_t vs1) (vpl_sels_f L.(vs0 @ vs1) sl)


let rec steel_intro_vprop_of_list_append #opened (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list vs0 `star` vprop_of_list vs1) (fun () -> vprop_of_list L.(vs0@vs1))
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> split_vars_list vs0 vs1 (sel_list L.(vs0@vs1) h1)
                        == (sel_list vs0 h0, sel_list vs1 h0))
      (decreases vs0)
  = match vs0 with
    | [] -> change_equal_slprop (vprop_of_list vs0) emp;
           change_equal_slprop (vprop_of_list vs1) (vprop_of_list L.(vs0@vs1))
    | v0 :: vs0' ->
           change_equal_slprop (vprop_of_list (vs0)) (VUnit v0 `star` vprop_of_list vs0');
           (**) let sl_v0   = gget' v0 in
           steel_intro_vprop_of_list_append vs0' vs1;
           (**) let sl_vs01 = gget (vprop_of_list L.(vs0'@vs1)) in
           (**) split_vars__cons v0 vs0' vs1 sl_v0 (vpl_sels L.(vs0' @ vs1) sl_vs01);
           change_equal_slprop (VUnit v0 `star` vprop_of_list L.(vs0'@vs1)) (vprop_of_list L.(vs0@vs1))

let steel_intro_vprop_of_list_append_f #opened (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list vs0 `star` vprop_of_list vs1) (fun () -> vprop_of_list L.(vs0@vs1))
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel_f L.(vs0@vs1) h1 == append_vars (sel_f vs0 h0) (sel_f vs1 h0))
  =
    steel_intro_vprop_of_list_append vs0 vs1;
    let sl = gget (vprop_of_list L.(vs0@vs1)) in
    Ll.map_append Mkvprop'?.t vs0 vs1;
    assert (vprop_list_sels_t L.(vs0 @ vs1) == L.(vprop_list_sels_t vs0 @ vprop_list_sels_t vs1))
        by T.(norm [delta_only [`%vprop_list_sels_t]]; smt ());
    Fl.splitAt_ty_of_d (vprop_list_sels_t vs0) (vprop_list_sels_t vs1) (vpl_sels L.(vs0 @ vs1) sl);
    Fl.splitAt_ty_append (vprop_list_sels_t vs0) (vprop_list_sels_t vs1) (vpl_sels_f L.(vs0 @ vs1) sl)


let rec steel_change_swap (#opened:Mem.inames)
          (vs0 : vprop_list) (i : nat {i <= L.length vs0 - 2})
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list (Perm.list_swap i vs0))
      (requires fun _ -> True) (ensures fun h0 () h1 ->
        sel_list (Perm.list_swap i vs0) h1 === Dl.dlist_swap i (sel_list vs0 h0))
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

let rec steel_change_perm_aux (#opened:Mem.inames)
          (n : nat) (vs0 vs1 : (l:vprop_list{L.length l == n}))
          (fs : list (i:nat{i <= n-2}))
          (eqv : squash (vs1 == Perm.apply_perm_r (Perm.comp_list (L.map (Perm.perm_f_swap #n) fs)) vs0))
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list vs1)
      (requires fun _ -> True) (ensures fun h0 () h1 ->
        sel_list vs1 h1 == Dl.apply_pequiv (vequiv_perm_sl (Perm.comp_list (L.map Perm.perm_f_swap fs)))
                                           (sel_list vs0 h0))
      (decreases fs)
  =
  let sl0  = gget (vprop_of_list vs0) in
  match fs with
  | []       -> change_equal_slprop (vprop_of_list vs0) (vprop_of_list vs1)
  | f0 :: fs' -> let pfs = Perm.comp_list (L.map (Perm.perm_f_swap #n) fs') in
               let vs' = Perm.apply_perm_r pfs vs0 in
               steel_change_perm_aux n vs0 vs' fs' ();
               let sl1' : sl_list vs' =
                 Dl.apply_pequiv #(vprop_list_sels_t vs0) #(vprop_list_sels_t vs')
                                  (vequiv_perm_sl (U.cast (Perm.perm_f (L.length vs0)) pfs))
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

let steel_change_perm (#vs0 #vs1 : vprop_list) (#opened:Mem.inames) (f : vequiv_perm vs0 vs1)
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel_f vs1 h1 == extract_vars f (sel_f vs0 h0))
  =
    let sl0 = gget (vprop_of_list vs0) in
    Fl.apply_perm_r_of_d f (vpl_sels vs0 sl0);
    steel_change_perm_aux (L.length vs0) vs0 vs1 (Perm.perm_f_to_swap f) ()

#push-options "--ifuel 1 --z3rlimit 20"
// ALT? use steel equiv
let rec elim_filter_mask #opened (vs : vprop_list) (mask : Ll.vec (L.length vs) bool)
  : SteelGhost unit opened
      (vprop_of_list Msk.(filter_mask mask vs) `star`
       vprop_of_list Msk.(filter_mask (mask_not mask) vs))
      (fun () -> vprop_of_list vs)
      (requires fun _ -> True) Msk.(ensures fun h0 () h1 ->
          sel_list (filter_mask mask vs) h0 == filter_mask_dl mask _ (sel_list vs h1) /\
          sel_list (filter_mask (mask_not mask) vs) h0 ==
            filter_mask_dl (mask_not mask) _ (sel_list vs h1))
      (decreases vs)
  = Msk.(match mask, vs with
  | [], [] ->
        change_equal_slprop
           (vprop_of_list (filter_mask mask vs) `star`
            vprop_of_list (filter_mask (Msk.mask_not mask) vs))
           (vprop_of_list vs `star` emp)
  | true  :: mask', v0 :: vs' ->
        (**) let mask' : Ll.vec (L.length vs') bool = mask' in
        (**) let sl1_t : Ghost.erased (t_of (vprop_of_list (filter_mask mask vs)))
        (**)           = gget (vprop_of_list (filter_mask mask vs)) in
        (**) let sl1_f : Ghost.erased (t_of (vprop_of_list (filter_mask (Msk.mask_not mask) vs)))
        (**)           = gget (vprop_of_list (filter_mask (Msk.mask_not mask) vs)) in
        change_equal_slprop (vprop_of_list (filter_mask mask vs))
                            (VUnit v0 `star` vprop_of_list (filter_mask mask' vs'));
        change_equal_slprop (vprop_of_list (filter_mask (Msk.mask_not mask ) vs ))
                            (vprop_of_list (filter_mask (Msk.mask_not mask') vs'));
        elim_filter_mask vs' mask';
        change_equal_slprop (VUnit v0 `star` vprop_of_list vs') (vprop_of_list vs);
        (**) let sl0 : Ghost.erased (t_of (vprop_of_list vs)) = gget (vprop_of_list vs) in
        (**) let l0  : sl_list vs = vpl_sels vs sl0 in
        (**) assert (vpl_sels (filter_mask mask vs) sl1_t === filter_mask_dl mask _ l0);
        (**) assert (vpl_sels _ sl1_f === filter_mask_dl (Msk.mask_not mask) _ l0)
  | false :: mask', v0 :: vs' ->
        (**) let mask' : Ll.vec (L.length vs') bool = mask'           in
        (**) let sl1_t = gget (vprop_of_list (filter_mask mask vs)) in
        (**) let sl1_f = gget (vprop_of_list (filter_mask (Msk.mask_not mask) vs)) in
        change_equal_slprop (vprop_of_list (filter_mask mask vs))
                            (vprop_of_list (filter_mask mask' vs'));
        change_equal_slprop (vprop_of_list (filter_mask (Msk.mask_not mask) vs))
                            (VUnit v0 `star` vprop_of_list (filter_mask (Msk.mask_not mask') vs'));
        elim_filter_mask vs' mask';
        change_equal_slprop (VUnit v0 `star` vprop_of_list vs') (vprop_of_list vs);
        (**) let sl0 = gget (vprop_of_list vs)        in
        (**) let l0  : sl_list vs = vpl_sels vs sl0 in
        (**) assert (vpl_sels _ sl1_t === filter_mask_dl mask _ l0);
        (**) assert (vpl_sels _ sl1_f === filter_mask_dl (Msk.mask_not mask) _ l0)
  )

let rec intro_filter_mask #opened (vs : vprop_list) (mask : Ll.vec (L.length vs) bool)
  : SteelGhost unit opened
      (vprop_of_list vs)
      (fun () -> vprop_of_list Msk.(filter_mask mask vs) `star`
              vprop_of_list Msk.(filter_mask (mask_not mask) vs))
      (requires fun _ -> True) Msk.(ensures fun h0 () h1 ->
          sel_list (filter_mask mask vs) h1 == filter_mask_dl mask _ (sel_list vs h0) /\
          sel_list (filter_mask (Msk.mask_not mask) vs) h1 ==
            filter_mask_dl (Msk.mask_not mask) _ (sel_list vs h0))
      (decreases vs)
  = Msk.(match mask, vs with
  | [], [] ->
        change_equal_slprop
           (vprop_of_list vs `star` emp)
           (vprop_of_list (filter_mask mask vs) `star`
            vprop_of_list (filter_mask (Msk.mask_not mask) vs))
  | true  :: mask', v0 :: vs' ->
        (**) let mask' : Ll.vec (L.length vs') bool = mask' in
        (**) let sl0 : Ghost.erased (t_of (vprop_of_list vs)) = gget (vprop_of_list vs) in
        (**) let l0  : sl_list vs = vpl_sels vs sl0 in
        change_equal_slprop (vprop_of_list vs) (VUnit v0 `star` vprop_of_list vs');
        intro_filter_mask vs' mask';
        change_equal_slprop (VUnit v0 `star` vprop_of_list (filter_mask mask' vs'))
                            (vprop_of_list (filter_mask mask vs));
        change_equal_slprop (vprop_of_list (filter_mask (Msk.mask_not mask') vs'))
                            (vprop_of_list (filter_mask (Msk.mask_not mask ) vs ));
        (**) let sl1_t : Ghost.erased (t_of (vprop_of_list (filter_mask mask vs)))
        (**)           = gget (vprop_of_list (filter_mask mask vs)) in
        (**) let sl1_f : Ghost.erased (t_of (vprop_of_list (filter_mask (Msk.mask_not mask) vs)))
        (**)           = gget (vprop_of_list (filter_mask (Msk.mask_not mask) vs)) in
        (**) let l1_t  : sl_list (filter_mask mask vs) = vpl_sels (filter_mask mask vs) sl1_t in
        (**) let l1_t' : sl_list (filter_mask mask vs) = U.cast _ (filter_mask_dl mask _ l0) in
        (**) assert (l1_t == l1_t');
        (**) assert (vpl_sels _ sl1_f === filter_mask_dl (Msk.mask_not mask) _ l0)
  | false :: mask', v0 :: vs' ->
        (**) let mask' : Ll.vec (L.length vs') bool = mask' in
        (**) let sl0 = gget (vprop_of_list vs)            in
        (**) let l0  : sl_list vs = vpl_sels vs sl0     in
        change_equal_slprop (vprop_of_list vs) (VUnit v0 `star` vprop_of_list vs');
        intro_filter_mask vs' mask';
        change_equal_slprop (vprop_of_list (filter_mask mask' vs'))
                            (vprop_of_list (filter_mask mask vs));
        change_equal_slprop (VUnit v0 `star` vprop_of_list (filter_mask (Msk.mask_not mask') vs'))
                            (vprop_of_list (filter_mask (Msk.mask_not mask) vs));
        (**) let sl1_t = gget (vprop_of_list (filter_mask mask vs))                in
        (**) let sl1_f = gget (vprop_of_list (filter_mask (Msk.mask_not mask) vs)) in
        (**) assert (vpl_sels _ sl1_t === filter_mask_dl mask _ l0);
        (**) assert (vpl_sels _ sl1_f === filter_mask_dl (Msk.mask_not mask) _ l0)
  )
#pop-options


let intro_elim_filter_mask_append_lem
      (vs : vprop_list) (m : Ll.vec (L.length vs) bool)
      (sl : sl_list vs) (sl0 : sl_list Msk.(filter_mask m vs)) (sl1 : sl_list Msk.(filter_mask (mask_not m) vs))
  : Lemma (requires sl0 == Msk.filter_mask_dl m _ sl /\ sl1 == Msk.filter_mask_dl (Msk.mask_not m) _ sl)
          (ensures  Fl.flist_of_d sl == append_vars_mask m (Fl.flist_of_d sl0) (Fl.flist_of_d sl1))
  =
    Msk.filter_mask_f_dl_f m _ (Fl.flist_of_d sl);
    assert (Fl.flist_of_d sl0 == Msk.filter_mask_fl m _ (Fl.flist_of_d sl));
    Msk.filter_mask_f_dl_f (Msk.mask_not m) _ (Fl.flist_of_d sl);
    append_filter_vars_mask m (Fl.flist_of_d sl)

let elim_filter_mask_append (#opened : Mem.inames) (vs : vprop_list) (m : Ll.vec (L.length vs) bool)
  : SteelGhost unit opened
      (vprop_of_list Msk.(filter_mask           m  vs) `star` 
       vprop_of_list Msk.(filter_mask (mask_not m) vs))
      (fun () -> vprop_of_list vs)
      (requires fun _ -> True) (ensures fun h0 () h1 ->
          sel_f vs h1 == append_vars_mask m (sel_f Msk.(filter_mask m vs) h0)
                                            (sel_f Msk.(filter_mask (mask_not m) vs) h0))
  =
    let sl0 = gget (vprop_of_list Msk.(filter_mask           m  vs)) in
    let sl1 = gget (vprop_of_list Msk.(filter_mask (mask_not m) vs)) in
    elim_filter_mask vs m;
    let sl  = gget (vprop_of_list vs)                                in
    intro_elim_filter_mask_append_lem vs m (vpl_sels _ sl) (vpl_sels _ sl0) (vpl_sels _ sl1)

let intro_filter_mask_append (#opened : Mem.inames) (vs : vprop_list) (m : Ll.vec (L.length vs) bool)
  : SteelGhost unit opened
      (vprop_of_list vs)
      (fun () -> vprop_of_list Msk.(filter_mask           m  vs) `star` 
              vprop_of_list Msk.(filter_mask (mask_not m) vs))
      (requires fun _ -> True) (ensures fun h0 () h1 ->
          sel_f vs h0 == append_vars_mask m (sel_f Msk.(filter_mask m vs) h1)
                                            (sel_f Msk.(filter_mask (mask_not m) vs) h1))
  =
    let sl  = gget (vprop_of_list vs)                                in
    intro_filter_mask vs m;
    let sl0 = gget (vprop_of_list Msk.(filter_mask           m  vs)) in
    let sl1 = gget (vprop_of_list Msk.(filter_mask (mask_not m) vs)) in
    intro_elim_filter_mask_append_lem vs m (vpl_sels _ sl) (vpl_sels _ sl0) (vpl_sels _ sl1)
