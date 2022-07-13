module Experiment.Steel.VPropList

module T  = FStar.Tactics
module L  = FStar.List.Pure
module SH = Experiment.Steel.Steel
module Msk  = Learn.List.Mask


(***** [vprop_of_list'] *)

let rec vprop_of_list'_can_be_split (vs : vprop_list) (i : nat {i < L.length vs})
  : Lemma (ensures can_be_split (vprop_of_list' vs) (VUnit (L.index vs i))) (decreases vs)
  = let v :: vs = vs in
    if i = 0
    then can_be_split_star_l (VUnit v) (vprop_of_list' vs)
    else begin
      can_be_split_star_r (VUnit v) (vprop_of_list' vs);
      vprop_of_list'_can_be_split vs (i-1);
      can_be_split_trans (VUnit v `star` vprop_of_list' vs) (vprop_of_list' vs) (VUnit (L.index vs (i-1)))
    end

let rec vprop_of_list'_append (vs0 vs1 : vprop_list)
  : Lemma (ensures equiv (vprop_of_list' L.(vs0@vs1)) (vprop_of_list' vs0 `star` vprop_of_list' vs1))
          (decreases vs0)
  = match vs0 with
  | []     -> assert (equiv (vprop_of_list' vs1) (emp `star` vprop_of_list' vs1))
                by (init_resolve_tac ())
  | v :: vs -> let v0 = VUnit v in
             let vl0 = vprop_of_list' vs in
             let vl1 = vprop_of_list' vs1 in
             let vl2 = vprop_of_list' L.(vs @ vs1) in
             assert_norm (vprop_of_list' L.((v :: vs) @ vs1) == v0 `star` vl2);
             equiv_refl v0;
             vprop_of_list'_append vs vs1;
             star_congruence v0       vl2
                             v0 (vl0 `star` vl1);
             star_associative v0 vl0 vl1;
             equiv_sym ((v0 `star` vl0) `star` vl1) (v0 `star` (vl0 `star` vl1));
             
             equiv_trans (v0 `star` vl2)
                         (v0 `star` (vl0 `star` vl1))
                         ((v0 `star` vl0) `star` vl1);
             assert_norm (vprop_of_list' (v :: vs) `star` vprop_of_list' vs1
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
  : Lemma (ensures equiv (vprop_of_list' (flatten_vprop ve)) vp) (decreases ve)
  = match ve with
  | VeEmp       -> equiv_refl emp
  | VeUnit v    -> assert (equiv (VUnit v `star` emp) (VUnit v))
                      by (init_resolve_tac ())
  | VeStar #vp0 ve0 #vp1 ve1 ->
           flatten_vprop_VStar ve0 ve1;
           vprop_of_list'_append (flatten_vprop ve0) (flatten_vprop ve1);
           vprop_equiv_flat vp0 ve0;
           vprop_equiv_flat vp1 ve1;
           star_congruence (vprop_of_list' (flatten_vprop ve0)) (vprop_of_list' (flatten_vprop ve1)) vp0 vp1;
           equiv_trans (vprop_of_list' L.(flatten_vprop ve0 @ flatten_vprop ve1))
                       (vprop_of_list' (flatten_vprop ve0) `star` vprop_of_list' (flatten_vprop ve1))
                       (vp0 `star` vp1)

(***** [vprop_of_list] *)

let vprop_of_list_hp (vs : vprop_list)
  = hp_of (vprop_of_list' vs)

let vprop_of_list_sel' (vs : vprop_list) : selector' (sl_f vs) (vprop_of_list_hp vs)
  = fun (h : Mem.hmem (vprop_of_list_hp vs)) ->
    Fl.flist_of_g (Fl.mk_flist_g (vprop_list_sels_t vs) (fun i ->
      (**) vprop_of_list'_can_be_split vs i;
      (**) can_be_split_interp (vprop_of_list' vs) (VUnit (L.index vs i)) h;
      (L.index vs i).sel h
    ))

#push-options "--fuel 1 --ifuel 0"
let vprop_of_list_sel'_depends_only_on
      (vs : vprop_list) (m0 : Mem.hmem (vprop_of_list_hp vs)) (m1 : Mem.mem {Mem.disjoint m0 m1})
  : Lemma (vprop_of_list_sel' vs m0 == vprop_of_list_sel' vs (Mem.join m0 m1))
  = Fl.flist_extensionality (vprop_of_list_sel' vs m0) (vprop_of_list_sel' vs (Mem.join m0 m1))
      (fun i -> vprop_of_list'_can_be_split vs i;
             can_be_split_interp (vprop_of_list' vs) (VUnit (L.index vs i)) m0)

let vprop_of_list_sel'_depends_only_on_core
      (vs : vprop_list) (m0 : Mem.hmem (vprop_of_list_hp vs))
  : Lemma (vprop_of_list_sel' vs m0 == vprop_of_list_sel' vs (Mem.core_mem m0))
  = Fl.flist_extensionality (vprop_of_list_sel' vs m0) (vprop_of_list_sel' vs (Mem.core_mem m0))
      (fun i -> vprop_of_list'_can_be_split vs i;
             can_be_split_interp (vprop_of_list' vs) (VUnit (L.index vs i)) m0)
#pop-options

let vprop_of_list_sel (vs : vprop_list) : selector (sl_f vs) (vprop_of_list_hp vs)
  =
    (**) FStar.Classical.forall_intro_2 (vprop_of_list_sel'_depends_only_on      vs);
    (**) FStar.Classical.forall_intro   (vprop_of_list_sel'_depends_only_on_core vs);
    vprop_of_list_sel' vs


let vprop_of_list_equiv (vs : vprop_list)
  : Lemma (vprop_of_list vs `equiv` vprop_of_list' vs)
  = reveal_equiv (vprop_of_list vs) (vprop_of_list' vs)

let vprop_of_list_can_be_split (vs : vprop_list) (i : Ll.dom vs)
  : Lemma (vprop_of_list vs `can_be_split` VUnit (L.index vs i))
  = reveal_can_be_split ();
    vprop_of_list'_can_be_split vs i

let vprop_of_list_interp (vs : vprop_list) (m : Mem.mem) = ()
let vprop_of_list_sel_eq (vs : vprop_list) (i : Ll.dom vs) (m : hmem (vprop_of_list vs)) = ()

#push-options "--fuel 2 --ifuel 0 --z3rlimit 20"
let vprop_of_list_interp_cons (v : vprop') (vs : vprop_list) (m : Mem.mem)
  : Lemma ((Mem.interp (vprop_of_list_hp (v :: vs)) m <==> Mem.interp (v.hp `Mem.star` vprop_of_list_hp vs) m) /\
           (Mem.interp (vprop_of_list_hp (v :: vs)) m ==>
            vprop_of_list_sel (v :: vs) m == Fl.cons (v.sel m) (vprop_of_list_sel vs m)))
  =
    introduce Mem.interp (vprop_of_list_hp (v :: vs)) m ==>
              vprop_of_list_sel (v :: vs) m == Fl.cons (v.sel m) (vprop_of_list_sel vs m)
      with _ .
        let lhs = vprop_of_list_sel (v :: vs) m               in
        let rhs = Fl.cons (v.sel m) (vprop_of_list_sel vs m) in
        Fl.flist_extensionality lhs rhs
          (fun i ->
            if i > 0 then begin
              let u = L.index vs (i-1) in
              vprop_of_list'_can_be_split vs (i-1);
              can_be_split_interp (vprop_of_list' vs) (VUnit u) m;
              calc (==) {
                lhs i <: u.t;
              == { }
                (L.index (v :: vs) i).sel m;
              == { }
                u.sel m;
              == { }
                vprop_of_list_sel vs m (i-1);
              == { }
                rhs i;
              }
            end)
#pop-options

(*** operations *)

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


(**** Steel *)

// ALT? use steel equiv

let elim_vpl_nil (#opened : Mem.inames) (vs : vprop_list {vs==[]})
  : SteelGhost unit opened (vprop_of_list vs) (fun () -> emp)
      (requires fun _ -> True)
      (ensures  fun h0 _ _ -> sel_f vs h0 == Fl.nil /\ sel_list vs h0 == Dl.DNil)
  =
    let sl = gget_f vs in
    Fl.nil_uniq sl;
    rewrite_slprop (vprop_of_list vs) emp (fun m -> ())

let intro_vpl_nil (#opened : Mem.inames) (vs : vprop_list {vs==[]})
  : SteelGhost unit opened emp (fun () -> vprop_of_list vs)
      (requires fun _ -> True)
      (ensures  fun _ _ h1 -> sel_f vs h1 == Fl.nil /\ sel_list vs h1 == Dl.DNil)
  =
    rewrite_slprop emp (vprop_of_list vs) (fun m -> ());
    let sl = gget_f vs in
    Fl.nil_uniq sl

#push-options "--z3rlimit 50"
let elim_vpl_cons (#opened : Mem.inames) (v : vprop') (vs : vprop_list)
  =
    let sl  : Ghost.erased (sl_f (v :: vs)) = gget_f (v :: vs) in
    let sl' : Fl.flist (v.t :: vprop_list_sels_t vs) = sl in
    change_slprop
      (vprop_of_list (v :: vs)) (VUnit v `star` vprop_of_list vs)
      sl (Fl.head sl', Fl.tail sl')
      (fun m -> vprop_of_list_interp_cons v vs m;
             assert (vprop_of_list_sel (v :: vs) m == Fl.cons (v.sel m) (vprop_of_list_sel vs m));
             assert (v.sel m == Fl.head sl');
             Fl.tail_cons (v.sel m) (vprop_of_list_sel vs m);
             assert (vprop_of_list_sel vs m == Fl.tail sl'));
    let hd = gget' v   in
    let tl : Ghost.erased (sl_f vs) = gget_f vs in
    Fl.as_cons sl';
    Fl.dlist_of_f_cons (Fl.head sl') (Fl.tail sl');
    assert (Fl.dlist_of_f sl === Dl.DCons v.t hd (vprop_list_sels_t vs) (Fl.dlist_of_f tl))
#pop-options

let intro_vpl_cons (#opened : Mem.inames) (v : vprop') (vs : vprop_list)
  =
    let hd = gget' v                                 in
    let hd : v.t = Ghost.reveal hd                   in
    let tl = gget_f vs                               in
    let tl : sl_f vs = Ghost.reveal tl               in
    let sl : sl_f (v :: vs) = U.cast _ (Fl.cons hd tl) in
    change_slprop
      (VUnit v `star` vprop_of_list vs) (vprop_of_list (v :: vs))
      (hd, tl) sl
      (vprop_of_list_interp_cons v vs);
    Fl.dlist_of_f_cons hd tl


let rec elim_vpl_append_list (#opened : Mem.inames) (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list L.(vs0@vs1)) (fun () -> vprop_of_list vs0 `star` vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 ->
         Ll.map_append Mkvprop'?.t vs0 vs1;
         sel_list L.(vs0@vs1) h0 == Dl.append (sel_list vs0 h1) (sel_list vs1 h1))
      (decreases vs0)
  = match vs0 with
  | [] ->
       change_equal_slprop (vprop_of_list L.(vs0@vs1)) (vprop_of_list vs1);
       intro_vpl_nil vs0
  | v0 :: vs0' ->
       change_equal_slprop (vprop_of_list L.(vs0@vs1)) (vprop_of_list L.(v0 :: (vs0' @ vs1)));
       elim_vpl_cons v0 L.(vs0' @ vs1);
       elim_vpl_append_list vs0' vs1;
       intro_vpl_cons v0 vs0';
       change_equal_slprop (vprop_of_list L.(v0 :: vs0')) (vprop_of_list vs0)

let rec intro_vpl_append_list (#opened : Mem.inames) (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list vs0 `star` vprop_of_list vs1) (fun () -> vprop_of_list L.(vs0@vs1))
      (requires fun _ -> True)
      (ensures fun h0 () h1 ->
         Ll.map_append Mkvprop'?.t vs0 vs1;
         sel_list L.(vs0@vs1) h1 == Dl.append (sel_list vs0 h0) (sel_list vs1 h0))
      (decreases vs0)
  = match vs0 with
  | [] ->
       elim_vpl_nil vs0;
       change_equal_slprop (vprop_of_list vs1) (vprop_of_list L.(vs0@vs1))
  | v0 :: vs0' ->
       change_equal_slprop (vprop_of_list vs0) (vprop_of_list L.(v0 :: vs0'));
       elim_vpl_cons v0 vs0';
       intro_vpl_append_list vs0' vs1;
       intro_vpl_cons v0 L.(vs0' @ vs1);
       change_equal_slprop (vprop_of_list L.(v0 :: (vs0' @ vs1))) (vprop_of_list L.(vs0@vs1))

let elim_vpl_append #opened (vs0 vs1 : vprop_list)
  =
    elim_vpl_append_list vs0 vs1;
    let sl0 = gget_f vs0 in
    let sl1 = gget_f vs1 in
    Fl.dlist_of_f_append sl0 sl1

let intro_vpl_append #opened (vs0 vs1 : vprop_list)
  =
    let sl0 = gget_f vs0 in
    let sl1 = gget_f vs1 in
    intro_vpl_append_list vs0 vs1;
    Fl.dlist_of_f_append sl0 sl1


let rec change_vpl_swap (#opened:Mem.inames)
          (vs0 : vprop_list) (i : nat {i <= L.length vs0 - 2})
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list (Perm.list_swap i vs0))
      (requires fun _ -> True) (ensures fun h0 () h1 ->
        sel_list (Perm.list_swap i vs0) h1 === Dl.dlist_swap i (sel_list vs0 h0))
      (decreases i)
  = if i = 0
    then begin
      let v0 :: v1 :: vs = vs0 in
      change_equal_slprop (vprop_of_list vs0) (vprop_of_list (v0 :: v1 :: vs));
      elim_vpl_cons  v0 (v1 :: vs);
      elim_vpl_cons  v1       vs;
      intro_vpl_cons v0       vs;
      intro_vpl_cons v1 (v0 :: vs);
      change_equal_slprop (vprop_of_list (v1 :: v0 :: vs)) (vprop_of_list (Perm.list_swap i vs0))
    end else begin
      let v0 :: vs = vs0 in
      change_equal_slprop (vprop_of_list vs0) (vprop_of_list (v0 :: vs));
      elim_vpl_cons  v0 vs;
      change_vpl_swap vs (i-1);
      intro_vpl_cons v0 (Perm.list_swap (i-1) vs);
      change_equal_slprop (vprop_of_list (v0 :: Perm.list_swap (i-1) vs)) (vprop_of_list (Perm.list_swap i vs0))
    end

let rec change_vpl_perm_aux (#opened:Mem.inames)
          (n : nat) (vs0 vs1 : (l:vprop_list{L.length l == n}))
          (fs : list (i:nat{i <= n-2}))
          (eqv : squash (vs1 == Perm.apply_perm_r (Perm.comp_list (L.map (Perm.perm_f_swap #n) fs)) vs0))
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list vs1)
      (requires fun _ -> True) (ensures fun h0 () h1 ->
        sel_list vs1 h1 == Dl.apply_pequiv (vequiv_perm_sl (Perm.comp_list (L.map Perm.perm_f_swap fs)))
                                           (sel_list vs0 h0))
      (decreases fs)
  =
  let sl0  = gget_list vs0 in
  match fs with
  | [] ->
      change_equal_slprop (vprop_of_list vs0) (vprop_of_list vs1)
  | f0 :: fs' ->
      let pfs = Perm.comp_list (L.map (Perm.perm_f_swap #n) fs') in
      let vs' = Perm.apply_perm_r pfs vs0 in
      change_vpl_perm_aux n vs0 vs' fs' ();
      let sl1' : sl_list vs' =
        Dl.apply_pequiv #(vprop_list_sels_t vs0) #(vprop_list_sels_t vs')
                         (vequiv_perm_sl (U.cast (Perm.perm_f (L.length vs0)) pfs)) sl0 in
      change_vpl_swap vs' f0;
      Perm.apply_swap_as_rec n f0 vs';
      Perm.apply_r_comp (Perm.perm_f_swap #n f0) pfs vs0;
      change_equal_slprop (vprop_of_list (Perm.list_swap f0 vs'))
                          (vprop_of_list vs1);
      let sl1 = gget_list vs1 in
      assert (Ghost.reveal sl1 === Dl.dlist_swap f0 sl1');
      Dl.apply_swap_as_rec n f0 sl1';
      Dl.apply_r_comp (Perm.perm_f_swap #n f0) pfs sl0

let change_vpl_perm (#vs0 #vs1 : vprop_list) (#opened:Mem.inames) (f : vequiv_perm vs0 vs1)
  =
    let sl0 = gget_list vs0 in
    Fl.apply_perm_r_of_d f sl0;
    change_vpl_perm_aux (L.length vs0) vs0 vs1 (Perm.perm_f_to_swap f) ()


#push-options "--ifuel 1 --z3rlimit 30"
let rec elim_vpl_filter_mask_list #opened (vs : vprop_list) (mask : Ll.vec (L.length vs) bool)
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
        change_equal_slprop (vprop_of_list (filter_mask mask vs)) (vprop_of_list vs);
        elim_vpl_nil (filter_mask (Msk.mask_not mask) vs)
  | true  :: mask', v0 :: vs' ->
        (**) let mask' : Ll.vec (L.length vs') bool = mask'         in
        (**) let sl1_t = gget_list (filter_mask mask vs)            in
        (**) let sl1_f = gget_list (filter_mask (mask_not mask) vs) in
        change_equal_slprop (vprop_of_list (     filter_mask mask vs ))
                            (vprop_of_list (v0 :: filter_mask mask' vs'));
        change_equal_slprop (vprop_of_list (filter_mask (mask_not mask ) vs ))
                            (vprop_of_list (filter_mask (mask_not mask') vs'));
        elim_vpl_cons v0 (filter_mask mask' vs');
        elim_vpl_filter_mask_list vs' mask';
        intro_vpl_cons v0 vs';
        change_equal_slprop (vprop_of_list (v0 :: vs')) (vprop_of_list vs);
        (**) let sl0 = gget_list vs                                 in
        (**) assert (Ghost.reveal sl1_t === filter_mask_dl mask _ sl0);
        (**) assert (Ghost.reveal sl1_f === filter_mask_dl (mask_not mask) _ sl0)
  | false :: mask', v0 :: vs' ->
        (**) let mask' : Ll.vec (L.length vs') bool = mask'         in
        (**) let sl1_t = gget_list (filter_mask mask vs)            in
        (**) let sl1_f = gget_list (filter_mask (mask_not mask) vs) in
        change_equal_slprop (vprop_of_list (filter_mask mask  vs ))
                            (vprop_of_list (filter_mask mask' vs'));
        change_equal_slprop (vprop_of_list (    filter_mask (mask_not mask ) vs ))
                            (vprop_of_list (v0 :: filter_mask (mask_not mask') vs'));
        elim_vpl_cons v0 (filter_mask (mask_not mask') vs');
        elim_vpl_filter_mask_list vs' mask';
        intro_vpl_cons v0 vs';
        change_equal_slprop (vprop_of_list (v0 :: vs')) (vprop_of_list vs);
        (**) let sl0 = gget_list vs                                 in
        (**) assert (Ghost.reveal sl1_t === filter_mask_dl mask _ sl0);
        (**) assert (Ghost.reveal sl1_f === filter_mask_dl (Msk.mask_not mask) _ sl0)
  )

let rec intro_vpl_filter_mask_list #opened (vs : vprop_list) (mask : Ll.vec (L.length vs) bool)
  : SteelGhost unit opened
      (vprop_of_list vs)
      (fun () -> vprop_of_list Msk.(filter_mask mask vs) `star`
              vprop_of_list Msk.(filter_mask (mask_not mask) vs))
      (requires fun _ -> True) Msk.(ensures fun h0 () h1 ->
          sel_list (filter_mask mask vs) h1 == filter_mask_dl mask _ (sel_list vs h0) /\
          sel_list (filter_mask (mask_not mask) vs) h1 ==
            filter_mask_dl (mask_not mask) _ (sel_list vs h0))
      (decreases vs)
  = Msk.(match mask, vs with
  | [], [] ->
        intro_vpl_nil (filter_mask (Msk.mask_not mask) vs);
        change_equal_slprop (vprop_of_list vs) (vprop_of_list (filter_mask mask vs))
  | true  :: mask', v0 :: vs' ->
        (**) let mask' : Ll.vec (L.length vs') bool = mask'         in
        (**) let sl0 = gget_list vs                                 in
        change_equal_slprop (vprop_of_list vs) (vprop_of_list (v0 :: vs'));
        elim_vpl_cons v0 vs';
        intro_vpl_filter_mask_list vs' mask';
        intro_vpl_cons v0 (filter_mask mask' vs');
        change_equal_slprop (vprop_of_list (v0 :: filter_mask mask' vs'))
                            (vprop_of_list (     filter_mask mask vs ));
        change_equal_slprop (vprop_of_list (filter_mask (mask_not mask') vs'))
                            (vprop_of_list (filter_mask (mask_not mask ) vs ));
        (**) let sl1_t = gget_list (filter_mask mask vs)            in
        (**) let sl1_f = gget_list (filter_mask (mask_not mask) vs) in
        (**) assert (Ghost.reveal sl1_t === filter_mask_dl mask _ sl0);
        (**) assert (Ghost.reveal sl1_f === filter_mask_dl (mask_not mask) _ sl0)
  | false :: mask', v0 :: vs' ->
        (**) let mask' : Ll.vec (L.length vs') bool = mask'         in
        (**) let sl0 = gget_list vs                                 in
        change_equal_slprop (vprop_of_list vs) (vprop_of_list (v0 :: vs'));
        elim_vpl_cons v0 vs';
        intro_vpl_filter_mask_list vs' mask';
        intro_vpl_cons v0 (filter_mask (mask_not mask') vs');
        change_equal_slprop (vprop_of_list (filter_mask mask' vs'))
                            (vprop_of_list (filter_mask mask  vs ));
        change_equal_slprop (vprop_of_list (v0 :: filter_mask (mask_not mask') vs'))
                            (vprop_of_list (    filter_mask (mask_not mask ) vs ));
        (**) let sl1_t = gget_list (filter_mask mask vs)            in
        (**) let sl1_f = gget_list (filter_mask (mask_not mask) vs) in
        (**) assert (Ghost.reveal sl1_t === filter_mask_dl mask _ sl0);
        (**) assert (Ghost.reveal sl1_f === filter_mask_dl (Msk.mask_not mask) _ sl0)
  )
#pop-options

let elim_vpl_filter_mask (#opened : Mem.inames) (vs : vprop_list) (mask : Ll.vec (L.length vs) bool)
  =
    elim_vpl_filter_mask_list vs mask;
    let sl = gget_f vs in
    Msk.filter_mask_f_dl_f mask _ sl;
    Msk.filter_mask_f_dl_f (Msk.mask_not mask) _ sl

let intro_vpl_filter_mask (#opened : Mem.inames) (vs : vprop_list) (mask : Ll.vec (L.length vs) bool)
  =
    let sl = gget_f vs in
    intro_vpl_filter_mask_list vs mask;
    Msk.filter_mask_f_dl_f mask _ sl;
    Msk.filter_mask_f_dl_f (Msk.mask_not mask) _ sl

let elim_vpl_filter_mask_append (#opened : Mem.inames) (vs : vprop_list) (m : Ll.vec (L.length vs) bool)
  =
    elim_vpl_filter_mask vs m;
    let sl  = gget_f vs in
    append_filter_vars_mask m sl

let intro_vpl_filter_mask_append (#opened : Mem.inames) (vs : vprop_list) (m : Ll.vec (L.length vs) bool)
  =
    let sl  = gget_f vs in
    intro_vpl_filter_mask vs m;
    append_filter_vars_mask m sl
