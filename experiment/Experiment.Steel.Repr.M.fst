module Experiment.Steel.Repr.M

module T = FStar.Tactics
module L = FStar.List.Pure


#set-options "--ide_id_info_off"

(*** Steel *)

let intro_subcomp_no_frame_pre
      (#a:Type)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
      (s_pre :  (h0 : rmem pre_g) -> Lemma
         (requires can_be_split pre_g pre_f /\
                   req_g h0)
         (ensures  req_f (focus_rmem h0 pre_f)))
      (s_post : (h0 : rmem pre_g) -> (x : a) -> (h1 : rmem (post_g x)) -> Lemma
         (requires can_be_split pre_g pre_f /\ can_be_split (post_g x) (post_f x) /\
                   req_g h0 /\ req_f (focus_rmem h0 pre_f) /\
                   ens_f (focus_rmem h0 pre_f) x (focus_rmem h1 (post_f x)))
         (ensures  ens_g h0 x h1))
  : squash (subcomp_no_frame_pre req_f ens_f req_g ens_g eq_pre eq_post)
  = _ by T.(
    set_guard_policy Force;
    norm [delta_only [`%subcomp_no_frame_pre]];
    let h0   = forall_intro () in
    let rq_g = implies_intro () in
    split ();
    
    apply_lemma (``@s_pre); split ();
      apply_lemma (`equiv_can_be_split); exact (``@eq_pre);
      hyp rq_g;

    let x    = forall_intro ()  in
    let h1   = forall_intro ()  in
    let en_f = implies_intro () in
    apply_lemma (``@s_post); explode ();
      apply_lemma (`equiv_can_be_split); exact (``@eq_pre);
      apply_lemma (`equiv_can_be_split); apply (``@eq_post);
      hyp rq_g;
      apply_lemma (``@s_pre); split ();
        apply_lemma (`equiv_can_be_split); exact (``@eq_pre);
        hyp rq_g;
      hyp en_f
  )

inline_for_extraction noextract
let unit_steel_subcomp_no_frame
      (#a : Type)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
      (sb_pre : squash (subcomp_no_frame_pre req_f ens_f req_g ens_g eq_pre eq_post))
      (f : unit_steel a pre_f post_f req_f ens_f)
  : unit_steel a pre_g post_g req_g ens_g
  =
    U.assert_by (can_be_split pre_g (pre_f `star` emp)) (fun () ->
      equiv_can_be_split pre_g pre_f;
      assert (can_be_split pre_f (pre_f `star` emp) /\ True)
        by (T.squash_intro (); selector_tactic ());
      can_be_split_trans pre_g pre_f (pre_f `star` emp));
    U.assert_by (equiv_forall post_g (fun x -> post_f x `star` emp)) (fun () ->
      introduce forall (x : a) . post_g x `equiv` (post_f x `star` emp)
      with (
        eq_post x;
        assert (post_f x `equiv` (post_f x `star` emp))
          by (init_resolve_tac ());
        equiv_trans (post_g x) (post_f x) (post_f x `star` emp)
      );
      equiv_forall_elim post_g (fun x -> post_f x `star` emp));
    Experiment.Steel.SteelHack.intro_subcomp_pre' req_f ens_f req_g ens_g #emp #True () ()
      (fun h0 -> ()) (fun h0 -> ()) (fun h0 x h1 -> ());
    Experiment.Steel.SteelHack.steel_subcomp a
      pre_f post_f req_f ens_f
      pre_g post_g req_g ens_g
      emp True () () ()
      f


(*** [vprop_list] *)

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

let rmem_star_eq (#p : vprop) (v0 v1 : vprop)
      (h : rmem p{can_be_split p (VStar v0 v1)})
  : Lemma (can_be_split p v0 /\ can_be_split p v1 /\
           h (VStar v0 v1) == (h v0, h v1))
  =
    can_be_split_star_l v0 v1;
    can_be_split_star_r v0 v1;
    can_be_split_trans p (VStar v0 v1) v0;
    can_be_split_trans p (VStar v0 v1) v1;
    // TODO: this is implied by [valid_rmem] but not exposed by the interface of [Steel.Effect.Common]
    //       maybe we can do the proofs in SteelGhost
    admit ()

let focus_rmem_feq (p q r : vprop) (h : rmem p)
  : Lemma (requires can_be_split p q /\ can_be_split q r)
          (ensures  can_be_split p r /\ focus_rmem h q r == h r)
  = can_be_split_trans p q r

#push-options "--ifuel 1 --fuel 1"
let rec sel_list_eq'_sub (#p : vprop) (vs : vprop_list)
                    (h : rmem p{can_be_split p (vprop_of_list vs)})
  : Lemma (sel_list' #p vs h == Fl.dlist_of_f_g (sel'_sub #p vs h))
  = match vs with
  | [] -> ()
  | v0 :: vs ->
       rmem_star_eq (VUnit v0) (vprop_of_list vs) h;
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
                     focus_rmem_feq p (vprop_of_list (v0 :: vs)) (VUnit (L.index (v0 :: vs) i)) h;
                     if i > 0 then begin
                       vprop_of_list_can_be_split vs (i - 1);
                       focus_rmem_feq p (vprop_of_list vs) (VUnit (L.index vs (i - 1))) h
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


let rec steel_elim_vprop_of_list_append #opened (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list L.(vs0@vs1)) (fun () -> vprop_of_list vs0 `star` vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> split_vars_list vs0 vs1 (sel_list (vs0@vs1) h0)
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
      (ensures fun h0 () h1 -> split_vars_list vs0 vs1 (sel_list (vs0@vs1) h0)
                        == (sel_list vs0 h1, sel_list vs1 h1))
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
      (ensures fun h0 () h1 -> split_vars vs0 vs1 (sel_f (vs0@vs1) h0)
                        == (sel_f vs0 h1, sel_f vs1 h1))
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
      (ensures fun h0 () h1 -> split_vars_list vs0 vs1 (sel_list (vs0@vs1) h1)
                        == (sel_list vs0 h0, sel_list vs1 h0))
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
      (ensures fun h0 () h1 -> split_vars vs0 vs1 (sel_f (vs0@vs1) h1)
                        == (sel_f vs0 h0, sel_f vs1 h0))
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

let rec steel_change_vequiv_aux (#opened:Mem.inames)
          (n : nat) (vs0 vs1 : (l:vprop_list{L.length l == n}))
          (fs : list (i:nat{i <= n-2}))
          (eqv : squash (vs1 == Perm.apply_perm_r (Perm.comp_list (L.map (Perm.perm_f_swap #n) fs)) vs0))
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list vs1)
      (requires fun _ -> True) (ensures fun h0 () h1 ->
        sel_list vs1 h1 == Dl.apply_pequiv (vequiv_sl (Perm.comp_list (L.map Perm.perm_f_swap fs)))
                                           (sel_list vs0 h0))
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
      (ensures fun h0 () h1 -> sel_f vs1 h1 == extract_vars f (sel_f vs0 h0))
  =
    let sl0 = gget (vprop_of_list vs0) in
    Fl.apply_perm_r_of_d f (vpl_sels vs0 sl0);
    steel_change_vequiv_aux (L.length vs0) vs0 vs1 (Perm.perm_f_to_swap f) ()


(*** [repr_steel_t] *)

inline_for_extraction noextract
let steel_of_repr
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      (f : repr_steel_t a tr.r_pre tr.r_post tr.r_req tr.r_ens)
  : unit_steel a pre post req ens
  =
    tr.r_pre_eq ();
    equiv_can_be_split pre (vprop_of_list tr.r_pre);
    introduce forall (x : a) . can_be_split (post x) (vprop_of_list (tr.r_post x))
      with (tr.r_post_eq x;
            equiv_can_be_split (post x) (vprop_of_list (tr.r_post x)));
    FStar.Classical.forall_intro tr.r_req_eq;
    FStar.Classical.forall_intro_3 tr.r_ens_eq;
    unit_steel_subcomp_no_frame
      _ _ req ens
      (tr.r_pre_eq ()) (fun x -> tr.r_post_eq x)
      ()
      f

// I was expecting this to be needed for repr_steel_of_steel, but the proof succeeds without it
let focus_rmem_trans (p q r : vprop) (h : rmem p)
  : Lemma (requires can_be_split p q /\ can_be_split q r)
          (ensures  can_be_split p r /\ focus_rmem (focus_rmem h q) r == focus_rmem h r)
  = can_be_split_trans p q r;
    introduce forall (r0 : vprop {can_be_split r r0}) .
        (focus_rmem (focus_rmem h q) r) r0 == (focus_rmem h r) r0
      with _ by T.(trefl ());
    FExt.extensionality_g _ _ (focus_rmem (focus_rmem h q) r) (focus_rmem h r)

inline_for_extraction noextract
let repr_steel_of_steel
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      ($f  : unit_steel a pre post req ens)
  : repr_steel_t a tr.r_pre tr.r_post tr.r_req tr.r_ens
  =
    tr.r_pre_eq ();
    equiv_can_be_split pre (vprop_of_list tr.r_pre);
    introduce forall (x : a) . can_be_split (post x) (vprop_of_list (tr.r_post x))
      with (tr.r_post_eq x;
            equiv_can_be_split (post x) (vprop_of_list (tr.r_post x)));
    FStar.Classical.forall_intro tr.r_req_eq;
    FStar.Classical.forall_intro_3 tr.r_ens_eq;
    let pre_eq_rev : squash (vprop_of_list tr.r_pre `equiv` pre) =
      tr.r_pre_eq (); equiv_sym pre (vprop_of_list tr.r_pre)    in
    let post_eq_rev (x : a) : squash (vprop_of_list (tr.r_post x) `equiv` post x) =
      tr.r_post_eq x; equiv_sym (post x) (vprop_of_list (tr.r_post x))           in
    unit_steel_subcomp_no_frame
      req ens _ _
      pre_eq_rev post_eq_rev
      (intro_subcomp_no_frame_pre _ _ _ _ _ _
        (fun h0 -> tr.r_req_eq (focus_rmem h0 pre))
        (fun h0 x h1 -> tr.r_ens_eq (focus_rmem h0 pre) x (focus_rmem h1 (post x))))
      f


(***** Monad combiners *)  

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
      (forall (x : a) (sl1 : sl_f (itm x)) .
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
        (exists (x : a) (sl1 : sl_f (itm x)) .
          tree_ens f cf (vpl_sels_f pre sl0) x sl1 /\
          tree_ens (g x) (cg x) sl1 y (vpl_sels_f (post y) sl2))
    ))
