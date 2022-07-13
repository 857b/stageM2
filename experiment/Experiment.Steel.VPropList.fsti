module Experiment.Steel.VPropList

module U    = Learn.Util
module L    = FStar.List.Pure
module Ll   = Learn.List
module Dl   = Learn.DList
module Fl   = Learn.FList
module Mem  = Steel.Memory
module Msk  = Learn.List.Mask
module Perm = Learn.Permutation

open Steel.Effect.Atomic


type vprop_list = list vprop'

(***** [vprop_of_list'] *)

[@@ __reduce__]
let rec vprop_of_list' (vpl : vprop_list) : vprop =
  match vpl with
  | [] -> emp
  | v :: vs -> VStar (VUnit v) (vprop_of_list' vs)

val vprop_of_list'_can_be_split (vs : vprop_list) (i : nat {i < L.length vs})
  : Lemma (can_be_split (vprop_of_list' vs) (VUnit (L.index vs i)))

val vprop_of_list'_append (vs0 vs1 : vprop_list)
  : Lemma (equiv (vprop_of_list' L.(vs0@vs1)) (vprop_of_list' vs0 `star` vprop_of_list' vs1))


noeq
type vprop_with_emp : vprop -> Type =
  | VeEmp  : vprop_with_emp emp
  | VeUnit : (v : vprop') -> vprop_with_emp (VUnit v)
  | VeStar : (#vl : vprop) -> (vel : vprop_with_emp vl) ->
             (#vr : vprop) -> (ver : vprop_with_emp vr) ->
             vprop_with_emp (VStar vl vr)
             
let rec flatten_vprop_aux (#vp : vprop) (ve : vprop_with_emp vp) (acc : vprop_list) : GTot vprop_list =
  match ve with
  | VeEmp -> acc
  | VeUnit vp' -> vp' :: acc
  | VeStar vp0 vp1 -> flatten_vprop_aux vp0 (flatten_vprop_aux vp1 acc)

let flatten_vprop (#vp : vprop) (ve : vprop_with_emp vp) : GTot vprop_list = flatten_vprop_aux ve []

val flatten_vprop_aux_eq (#vp : vprop) (ve : vprop_with_emp vp) (acc : vprop_list)
  : Lemma (flatten_vprop_aux ve acc == L.(flatten_vprop ve @ acc))

val flatten_vprop_VStar (#vp0 : vprop) (ve0 : vprop_with_emp vp0) (#vp1 : vprop) (ve1 : vprop_with_emp vp1)
  : Lemma (flatten_vprop (VeStar ve0 ve1) == L.(flatten_vprop ve0 @ flatten_vprop ve1))

val vprop_equiv_flat (vp : vprop) (ve : vprop_with_emp vp)
  : Lemma (equiv (vprop_of_list' (flatten_vprop ve)) vp)


noeq
type vprop_to_list (v : vprop) : (vs : vprop_list) -> Type =
  | VPropToList : (ve : vprop_with_emp v) -> vprop_to_list v (flatten_vprop ve)

let vprop_to_list_equiv' (#v : vprop) (#vs : vprop_list) (t : vprop_to_list v vs)
  : Lemma (v `equiv` vprop_of_list' vs)
  =
    let VPropToList ve = t in
    vprop_equiv_flat v ve;
    equiv_sym (vprop_of_list' vs) v


(***** selectors *)

let vprop_list_sels_t : vprop_list -> Dl.ty_list =
  L.map Mkvprop'?.t

unfold
let sl_t (vs : vprop_list) : Type = Fl.flist_g (vprop_list_sels_t vs)

unfold
let sl_f (vs : vprop_list) : Type = Fl.flist (vprop_list_sels_t vs)

unfold
let sl_list (vs : vprop_list) : Type = Dl.dlist (vprop_list_sels_t vs)

let vprop_list_sels_t_eq (vs : vprop_list) (i : nat {i < L.length vs})
  : Lemma (ensures L.index (vprop_list_sels_t vs) i == (L.index vs i).t)
          [SMTPat (L.index (vprop_list_sels_t vs) i)]
  = Ll.map_index Mkvprop'?.t vs i


(***** [vprop_of_list] *)

// We cannot use [sl_list vs] as selector type since it is in universe u#1, be [sl_f vs] works

val vprop_of_list_hp  (vs : vprop_list) : Mem.slprop u#1

val vprop_of_list_sel (vs : vprop_list) : selector (sl_f vs) (vprop_of_list_hp vs)

[@@__steel_reduce__]
let vprop_of_list_r (vs : vprop_list) : vprop' =
  {
    hp  = vprop_of_list_hp vs;
    t   = sl_f vs;
    sel = vprop_of_list_sel vs;
  }
unfold let vprop_of_list (vs : vprop_list) : vprop =
  VUnit (vprop_of_list_r vs)

val vprop_of_list_equiv (vs : vprop_list)
  : Lemma (vprop_of_list vs `equiv` vprop_of_list' vs)

val vprop_of_list_can_be_split (vs : vprop_list) (i : Ll.dom vs)
  : Lemma (vprop_of_list vs `can_be_split` VUnit (L.index vs i))

val vprop_of_list_interp (vs : vprop_list) (m : Mem.mem)
  : Lemma (Mem.interp (vprop_of_list_hp vs) m <==> Mem.interp (hp_of (vprop_of_list' vs)) m)

val vprop_of_list_sel_eq (vs : vprop_list) (i : Ll.dom vs) (m : hmem (vprop_of_list vs))
  : Lemma (
      (**) vprop_of_list_can_be_split vs i;
      (**) can_be_split_interp (vprop_of_list vs) (VUnit (L.index vs i)) m;
      vprop_of_list_sel vs m i == (L.index vs i).sel m)

val vprop_of_list_interp_cons (v : vprop') (vs : vprop_list) (m : Mem.mem)
  : Lemma ((Mem.interp (vprop_of_list_hp (v :: vs)) m <==> Mem.interp (v.hp `Mem.star` vprop_of_list_hp vs) m) /\
           (Mem.interp (vprop_of_list_hp (v :: vs)) m ==>
            vprop_of_list_sel (v :: vs) m == Fl.cons (v.sel m) (vprop_of_list_sel vs m)))

let vprop_to_list_equiv (#v : vprop) (#vs : vprop_list) (t : vprop_to_list v vs)
  : Lemma (v `equiv` vprop_of_list vs)
  =
    vprop_to_list_equiv' t;
    vprop_of_list_equiv vs;
    equiv_sym (vprop_of_list vs) (vprop_of_list' vs);
    equiv_trans v (vprop_of_list' vs) (vprop_of_list vs)

unfold
let sel_f (#p : vprop) (vs : vprop_list)
      (h : rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (vprop_of_list vs) /\ True)})
  : GTot (sl_f vs)
  = h (vprop_of_list vs)

unfold
let sel_list (#p : vprop) (vs : vprop_list)
      (h : rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (vprop_of_list vs) /\ True)})
  : GTot (sl_list vs)
  = Fl.dlist_of_f (h (vprop_of_list vs))


let gget' (#opened : Mem.inames) (p : vprop')
  : SteelGhost (Ghost.erased p.t) opened (VUnit p) (fun _ -> VUnit p)
      (requires fun _ -> True)
      (ensures  fun h0 x h1 -> frame_equalities (VUnit p) h0 h1 /\ Ghost.reveal x == h0 (VUnit p))
  = gget (VUnit p)

let gget_f (#opened : Mem.inames) (vs : vprop_list)
  : SteelGhost (Ghost.erased (sl_f vs)) opened (vprop_of_list vs) (fun _ -> vprop_of_list vs)
      (requires fun _ -> True)
      (ensures  fun h0 sl h1 -> frame_equalities (vprop_of_list vs) h0 h1 /\ Ghost.reveal sl == sel_f vs h0)
  = gget (vprop_of_list vs)

let gget_list (#opened : Mem.inames) (vs : vprop_list)
  : SteelGhost (Ghost.erased (sl_list vs)) opened (vprop_of_list vs) (fun _ -> vprop_of_list vs)
      (requires fun _ -> True)
      (ensures  fun h0 sl h1 -> frame_equalities (vprop_of_list vs) h0 h1 /\ Ghost.reveal sl == sel_list vs h0)
  = let sl = gget (vprop_of_list vs) in
    Fl.dlist_of_f sl

(*** operations *)

unfold
let split_vars (vs0 vs1 : vprop_list) (xs : sl_f L.(vs0 @ vs1))
  : sl_f vs0 & sl_f vs1
  =
    (**) Ll.map_append Mkvprop'?.t vs0 vs1;
    Fl.splitAt_ty (vprop_list_sels_t vs0) (vprop_list_sels_t vs1) xs

unfold
let split_vars_list (vs0 vs1 : vprop_list) (xs : sl_list L.(vs0 @ vs1))
  : sl_list vs0 & sl_list vs1
  =
    (**) Ll.map_append Mkvprop'?.t vs0 vs1;
    Dl.splitAt_ty (vprop_list_sels_t vs0) (vprop_list_sels_t vs1) xs

unfold
let append_vars (#vs0 #vs1 : vprop_list) (xs : sl_f vs0) (ys : sl_f vs1)
  : sl_f L.(vs0 @ vs1)
  =
    (**) Ll.map_append Mkvprop'?.t vs0 vs1;
    Fl.append xs ys

let split_vars_append (v0 v1 : vprop_list) (sl : sl_f L.(v0 @ v1)) ()
  : Lemma (sl == (let sls = split_vars v0 v1 sl in append_vars sls._1 sls._2))
  =
    Ll.pat_append ();
    Fl.splitAt_ty_append (vprop_list_sels_t v0) (vprop_list_sels_t v1) sl

let append_split_vars (v0 v1 : vprop_list) (sl0 : sl_f v0) (sl1 : sl_f v1) ()
  : Lemma (split_vars v0 v1 (append_vars sl0 sl1) == (sl0, sl1))
  =
    Ll.pat_append ();
    Fl.append_splitAt_ty (vprop_list_sels_t v0) (vprop_list_sels_t v1) sl0 sl1


let rew_append_var_inj (#t0 #t1 : vprop_list) (x0 x1 : sl_f t0) (y0 y1 : sl_f t1)
  : squash ((append_vars x0 y0 == append_vars x1 y1) <==> (x0 == x1 /\ y0 == y1))
  = Fl.append_splitAt_ty _ _ x0 y0; Fl.append_splitAt_ty _ _ x1 y1

let rew_append_var_inj'
    #tx0 (x0 : sl_f tx0) #tx1 (x1 : sl_f tx1)
    #ty0 (y0 : sl_f ty0) #ty1 (y1 : sl_f ty1)
    #teq (_ : squash (tx0 == tx1 /\ ty0 == ty1 /\ teq == L.(tx0 @ ty0)))
  : squash (eq2 #(sl_f teq) (append_vars #tx0 #ty0 x0 y0) (append_vars #tx1 #ty1 x1 y1)
        <==> (x0 == x1 /\ y0 == y1))
  = rew_append_var_inj x0 x1 y0 y1

val rew_forall_sl_f_app (v0 v1 : vprop_list) (p0 : sl_f L.(v0 @ v1) -> Type) (p1 : Type)
    (_ : squash ((forall (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1)) <==> p1))
  : squash ((forall (sl : sl_f L.(v0 @ v1)) . p0 sl) <==> p1)

val rew_exists_sl_f_app (v0 v1 : vprop_list) (p0 : sl_f L.(v0 @ v1) -> Type) (p1 : Type)
    (_ : squash ((exists (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1)) <==> p1))
  : squash ((exists (sl : sl_f L.(v0 @ v1)) . p0 sl) <==> p1)


let vequiv_perm : vprop_list -> vprop_list -> Type = Perm.pequiv #vprop'

unfold
let vequiv_perm_sl (#vs0 #vs1 : vprop_list) (f : vequiv_perm vs0 vs1)
  : Perm.pequiv (vprop_list_sels_t vs0) (vprop_list_sels_t vs1)
  = Perm.map_apply_r f Mkvprop'?.t vs0;
    U.cast #(Perm.perm_f (L.length vs0)) (Perm.perm_f (L.length (vprop_list_sels_t vs0))) f    

// TODO? only use the case of an injection (i.e. LV.eij_sl)
unfold
let extract_vars (#src #dst : vprop_list)
                 (p : vequiv_perm src dst)
                 (xs : sl_f src)
  : sl_f dst
  =
    Fl.apply_pequiv (vequiv_perm_sl p) xs

unfold
let extract_vars_f (src dst frame : vprop_list)
                   (p : vequiv_perm src L.(dst@frame))
                   (xs : sl_f src)
  : sl_f dst & sl_f frame
  =
    split_vars dst frame (extract_vars p xs)

let extract_vars_sym_l (#vs0 #vs1 : vprop_list) (f : vequiv_perm vs0 vs1) (xs : sl_f vs0)
  : Lemma (extract_vars (Perm.pequiv_sym f) (extract_vars f xs) == xs)
  =
    Fl.apply_pequiv_sym_l (vequiv_perm_sl f) xs

let filter_sl
      (#vs : vprop_list) (mask : Msk.mask_t vs) (xs : sl_f vs)
  : sl_f (Msk.filter_mask mask vs)
  = Msk.filter_mask_fl mask (vprop_list_sels_t vs) xs


// ALT? direct definition
let append_vars_mask
      (#vs : vprop_list) (m : Msk.mask_t vs)
      (sl0 : sl_f Msk.(filter_mask m vs)) (sl1 : sl_f Msk.(filter_mask (mask_not m) vs))
  : sl_f vs
  =
    extract_vars (Msk.mask_pequiv_append' m vs) (append_vars sl0 sl1)

val append_vars_mask_index
      (#vs : vprop_list) (m : Msk.mask_t vs)
      (sl0 : sl_f Msk.(filter_mask m vs)) (sl1 : sl_f Msk.(filter_mask (mask_not m) vs))
      (i : Ll.dom vs)
  : Lemma (append_vars_mask m sl0 sl1 i
       == (if L.index m i then U.cast _ (sl0 Msk.(mask_push m i))
                          else U.cast _ (sl1 Msk.(mask_push (mask_not m) i))))

val append_filter_vars_mask
      (#vs : vprop_list) (m : Msk.mask_t vs) (sl : sl_f vs)
  : Lemma (append_vars_mask m (filter_sl m sl) (filter_sl (Msk.mask_not m) sl) == sl)

val filter_append_vars_mask
      (#vs : vprop_list) (m : Msk.mask_t vs)
      (sl0 : sl_f Msk.(filter_mask m vs)) (sl1 : sl_f Msk.(filter_mask (mask_not m) vs))
  : Lemma (filter_sl               m  (append_vars_mask m sl0 sl1) == sl0 /\
           filter_sl (Msk.mask_not m) (append_vars_mask m sl0 sl1) == sl1)


(**** Steel *)

val elim_vpl_nil (#opened : Mem.inames) (vs : vprop_list {vs==[]})
  : SteelGhost unit opened (vprop_of_list vs) (fun () -> emp)
      (requires fun _ -> True)
      (ensures  fun h0 _ _ -> sel_f    vs h0 == Fl.nil /\
                           sel_list vs h0 == Dl.DNil)

val intro_vpl_nil (#opened : Mem.inames) (vs : vprop_list {vs==[]})
  : SteelGhost unit opened emp (fun () -> vprop_of_list vs)
      (requires fun _ -> True)
      (ensures  fun _ _ h1 -> sel_f    vs h1 == Fl.nil /\
                           sel_list vs h1 == Dl.DNil)

val elim_vpl_cons (#opened : Mem.inames) (v : vprop') (vs : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list (v :: vs)) (fun () -> VUnit v `star` vprop_of_list vs)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel_f    (v :: vs) h0 == Fl.cons    (h1 (VUnit v))   (sel_f    vs h1) /\
                            sel_list (v :: vs) h0 == Dl.DCons _ (h1 (VUnit v)) _ (sel_list vs h1))

val intro_vpl_cons (#opened : Mem.inames) (v : vprop') (vs : vprop_list)
  : SteelGhost unit opened
      (VUnit v `star` vprop_of_list vs) (fun () -> vprop_of_list (v :: vs))
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel_f    (v :: vs) h1 == Fl.cons    (h0 (VUnit v))   (sel_f    vs h0) /\
                            sel_list (v :: vs) h1 == Dl.DCons _ (h0 (VUnit v)) _ (sel_list vs h0))


val elim_vpl_append (#opened : Mem.inames) (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list L.(vs0@vs1)) (fun () -> vprop_of_list vs0 `star` vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel_f L.(vs0@vs1) h0 == append_vars (sel_f vs0 h1) (sel_f vs1 h1))

val intro_vpl_append (#opened : Mem.inames) (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list vs0 `star` vprop_of_list vs1) (fun () -> vprop_of_list L.(vs0@vs1))
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel_f L.(vs0@vs1) h1 == append_vars (sel_f vs0 h0) (sel_f vs1 h0))


val change_vpl_perm (#vs0 #vs1 : vprop_list) (#opened:Mem.inames) (f : vequiv_perm vs0 vs1)
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel_f vs1 h1 == extract_vars f (sel_f vs0 h0))


val elim_vpl_filter_mask (#opened : Mem.inames) (vs : vprop_list) (mask : Ll.vec (L.length vs) bool)
  : SteelGhost unit opened
      (vprop_of_list Msk.(filter_mask mask vs) `star`
       vprop_of_list Msk.(filter_mask (mask_not mask) vs))
      (fun () -> vprop_of_list vs)
      (requires fun _ -> True) (ensures fun h0 () h1 ->
          sel_f Msk.(filter_mask mask vs) h0 == filter_sl mask (sel_f vs h1) /\
          sel_f Msk.(filter_mask (mask_not mask) vs) h0 == filter_sl (Msk.mask_not mask) (sel_f vs h1))

val intro_vpl_filter_mask (#opened : Mem.inames) (vs : vprop_list) (mask : Ll.vec (L.length vs) bool)
  : SteelGhost unit opened
      (vprop_of_list vs)
      (fun () -> vprop_of_list Msk.(filter_mask mask vs) `star`
              vprop_of_list Msk.(filter_mask (mask_not mask) vs))
      (requires fun _ -> True) (ensures fun h0 () h1 ->
          sel_f Msk.(filter_mask mask vs) h1 == filter_sl mask (sel_f vs h0) /\
          sel_f Msk.(filter_mask (mask_not mask) vs) h1 == filter_sl (Msk.mask_not mask) (sel_f vs h0))


val elim_vpl_filter_mask_append (#opened : Mem.inames) (vs : vprop_list) (m : Ll.vec (L.length vs) bool)
  : SteelGhost unit opened
      (vprop_of_list Msk.(filter_mask           m  vs) `star` 
       vprop_of_list Msk.(filter_mask (mask_not m) vs))
      (fun () -> vprop_of_list vs)
      (requires fun _ -> True) (ensures fun h0 () h1 ->
          sel_f vs h1 == append_vars_mask m (sel_f Msk.(filter_mask m vs) h0)
                                            (sel_f Msk.(filter_mask (mask_not m) vs) h0))

val intro_vpl_filter_mask_append (#opened : Mem.inames) (vs : vprop_list) (m : Ll.vec (L.length vs) bool)
  : SteelGhost unit opened
      (vprop_of_list vs)
      (fun () -> vprop_of_list Msk.(filter_mask           m  vs) `star` 
              vprop_of_list Msk.(filter_mask (mask_not m) vs))
      (requires fun _ -> True) (ensures fun h0 () h1 ->
          sel_f vs h0 == append_vars_mask m (sel_f Msk.(filter_mask m vs) h1)
                                            (sel_f Msk.(filter_mask (mask_not m) vs) h1))
