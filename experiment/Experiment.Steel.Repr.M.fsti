module Experiment.Steel.Repr.M

module U    = Learn.Util
module L    = FStar.List.Pure
module Dl   = Learn.DList
module Fl   = Learn.FList
module Ll   = Learn.List
module SE   = Steel.Effect
module SH   = Experiment.Steel.SteelHack
module Opt  = Learn.Option
module Mem  = Steel.Memory
module Perm = Learn.Permutation
module FExt = FStar.FunctionalExtensionality

open Steel.Effect
open Steel.Effect.Atomic


irreducible let __repr_M__ : unit = ()


(*** Steel *)

val focus_rmem_feq (p q r : vprop) (h : rmem p)
  : Lemma (requires can_be_split p q /\ can_be_split q r)
          (ensures  can_be_split p r /\ focus_rmem h q r == h r)

val focus_rmem_trans (p q r : vprop) (h : rmem p)
  : Lemma (requires can_be_split p q /\ can_be_split q r)
          (ensures  can_be_split p r /\ focus_rmem (focus_rmem h q) r == focus_rmem h r)


(* This does not seems provable from the interface of Steel.Effect
// Warning : this can drop some slprops
val change_can_be_split_slprop
      (#opened : Mem.inames)
      (p q : vprop) (_ : squash(can_be_split p q))
  : SteelGhost unit opened p (fun () -> q) (fun _ -> True) (fun h0 () h1 -> h1 q == h0 q)
*)

let subcomp_no_frame_pre
      (#a:Type)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
  : prop
  =
    forall (h0 : rmem pre_g) . (
     (**) equiv_can_be_split pre_g pre_f; (
     req_g h0 ==>
      (req_f (focus_rmem h0 pre_f) /\
      (forall (x : a) (h1 : rmem (post_g x)) . (
        (**) eq_post x; equiv_can_be_split (post_g x) (post_f x); (
        ens_f (focus_rmem h0 pre_f) x (focus_rmem h1 (post_f x)) ==>
        ens_g h0 x h1))))))

val intro_subcomp_no_frame_pre
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

inline_for_extraction noextract
val unit_steel_subcomp_no_frame
      (#a : Type)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
      (sb_pre : squash (subcomp_no_frame_pre req_f ens_f req_g ens_g eq_pre eq_post))
      ($f : SH.unit_steel a pre_f post_f req_f ens_f)
  : SH.unit_steel a pre_g post_g req_g ens_g

inline_for_extraction noextract
val unit_steel_ghost_subcomp_no_frame
      (#a : Type) (#opened : Mem.inames)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
      (sb_pre : squash (subcomp_no_frame_pre req_f ens_f req_g ens_g eq_pre eq_post))
      ($f : SH.unit_steel_ghost a opened pre_f post_f req_f ens_f)
  : SH.unit_steel_ghost a opened pre_g post_g req_g ens_g


(*** [vprop_list] *)

type vprop_list = list vprop'

[@@ __reduce__]
let rec vprop_of_list' (vpl : vprop_list) : vprop =
  match vpl with
  | [] -> emp
  | v :: vs -> VStar (VUnit v) (vprop_of_list' vs)

let vprop_of_list = vprop_of_list'

val vprop_of_list_can_be_split (vs : vprop_list) (i : nat {i < L.length vs})
  : Lemma (can_be_split (vprop_of_list vs) (VUnit (L.index vs i)))

val vprop_of_list_append (vs0 vs1 : vprop_list)
  : Lemma (equiv (vprop_of_list L.(vs0@vs1)) (vprop_of_list vs0 `star` vprop_of_list vs1))


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
  : Lemma (equiv (vprop_of_list (flatten_vprop ve)) vp)


(* ALT? dependent arrrow Fin.fin n -> _ *)

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

let rec vpl_sels (vs : vprop_list) (sl : t_of (vprop_of_list vs))
  : Tot (sl_list vs) (decreases vs)
  = match (|vs, sl|) <: (vs : vprop_list & t_of (vprop_of_list vs)) with
  | (|[], _|) -> Dl.DNil
  | (|v0 :: vs, sl|) -> Dl.DCons v0.t sl._1 _ (vpl_sels vs sl._2)

unfold
let vpl_sels_f (vs : vprop_list) (sl : t_of (vprop_of_list vs)) : sl_f vs
  = Fl.flist_of_d (vpl_sels vs sl)

unfold
let sel_list' (#p : vprop) (vs : vprop_list)
      (h : rmem p{can_be_split p (vprop_of_list vs)})
  : GTot (sl_list vs)
  = vpl_sels vs (h (vprop_of_list vs))

unfold
let sel_list (#p : vprop) (vs : vprop_list)
      (h : rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (vprop_of_list vs) /\ True)})
  : GTot (sl_list vs)
  = sel_list' vs h

unfold
let sel_f (#p : vprop) (vs : vprop_list)
      (h : rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (vprop_of_list vs) /\ True)})
  : GTot (sl_f vs)
  = Fl.flist_of_d (sel_list vs h)

unfold
let sel (vs : vprop_list) (h : rmem (vprop_of_list vs))
  : GTot (sl_f vs)
  = sel_f vs h


/// Variant to be used when interacting with Steel
let sel' (vs : vprop_list) (h : rmem (vprop_of_list' vs))
  : sl_t vs
  = Fl.mk_flist_g (vprop_list_sels_t vs) (fun i ->
    (**) vprop_of_list_can_be_split vs i;
    h (VUnit (L.index vs i)))

let sel_f' (vs : vprop_list) (h : rmem (vprop_of_list' vs))
  : GTot (sl_f vs)
  = Fl.flist_of_g (sel' vs h)

val sel_list_eq' (vs : vprop_list) (h : rmem (vprop_of_list vs))
  : Lemma (sel_list vs h == Fl.dlist_of_f_g (sel' vs h))

let sel_f_eq' (vs : vprop_list) (h : rmem (vprop_of_list vs))
  : Lemma (sel_f vs h == sel_f' vs h)
  = sel_list_eq' vs h

val sel_eq' : squash (sel_f' == sel)


let gget' (#opened : Mem.inames) (p : vprop')
  : SteelGhost (Ghost.erased p.t) opened (VUnit p) (fun _ -> VUnit p)
               (requires fun _ -> True)
               (ensures fun h0 x h1 -> frame_equalities (VUnit p) h0 h1 /\ Ghost.reveal x == h0 (VUnit p))
  = gget (VUnit p)

let gget_f (#opened : Mem.inames) (vs : vprop_list)
  : SteelGhost (Ghost.erased (sl_f vs)) opened (vprop_of_list vs) (fun _ -> vprop_of_list vs)
               (requires fun _ -> True)
               (ensures fun h0 x h1 -> frame_equalities (vprop_of_list vs) h0 h1 /\
                                    Ghost.reveal x == sel_f vs h0)
  = let x = gget (vprop_of_list vs) in
    vpl_sels_f vs x


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

let split_vars__cons (v0 : vprop') (vs0 vs1 : vprop_list) (x0 : v0.t) (xs : sl_list L.(vs0@vs1))
  : Lemma (ensures split_vars_list (v0 :: vs0) vs1 (Dl.DCons v0.t x0 (vprop_list_sels_t L.(vs0@vs1)) xs)
               == (let xs0, xs1 = split_vars_list vs0 vs1 xs in
                   Dl.DCons v0.t x0 (vprop_list_sels_t vs0) xs0, xs1))
  = Ll.map_append Mkvprop'?.t vs0 vs1

unfold
let append_vars (#vs0 #vs1 : vprop_list) (xs : sl_f vs0) (ys : sl_f vs1)
  : sl_f L.(vs0 @ vs1)
  =
    (**) Ll.map_append Mkvprop'?.t vs0 vs1;
    Fl.append xs ys


val steel_elim_vprop_of_list_cons_f (#opened : Mem.inames) (v : vprop') (vs : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list (v :: vs)) (fun () -> VUnit v `star` vprop_of_list vs)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel_f (v :: vs) h0 == Fl.cons (h1 (VUnit v)) (sel_f vs h1))

val steel_intro_vprop_of_list_cons_f (#opened : Mem.inames) (v : vprop') (vs : vprop_list)
  : SteelGhost unit opened
      (VUnit v `star` vprop_of_list vs) (fun () -> vprop_of_list (v :: vs))
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel_f (v :: vs) h1 == Fl.cons (h0 (VUnit v)) (sel_f vs h0))

val steel_elim_vprop_of_list_append_f (#opened : Mem.inames) (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list L.(vs0@vs1)) (fun () -> vprop_of_list vs0 `star` vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel_f (vs0@vs1) h0 == append_vars (sel_f vs0 h1) (sel_f vs1 h1))

val steel_intro_vprop_of_list_append_f (#opened : Mem.inames) (vs0 vs1 : vprop_list)
  : SteelGhost unit opened
      (vprop_of_list vs0 `star` vprop_of_list vs1) (fun () -> vprop_of_list L.(vs0@vs1))
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel_f (vs0@vs1) h1 == append_vars (sel_f vs0 h0) (sel_f vs1 h0))


(***** [vequiv] *)

irreducible let __vequiv__ : unit = ()

type veq_eq_t (pre_n post_n : nat) = FExt.(Fin.fin post_n ^-> option (Fin.fin pre_n))

unfold
let veq_eq_sl (#pre #post : vprop_list) (e : veq_eq_t (L.length pre) (L.length post))
  : veq_eq_t (L.length (vprop_list_sels_t pre)) (L.length (vprop_list_sels_t post))
  = U.cast _ e

[@@__vequiv__]
noextract
let mk_veq_eq (pre_n post_n : nat) (f : Fin.fin post_n -> option (Fin.fin pre_n))
  : veq_eq_t pre_n post_n
  = FExt.on (Fin.fin post_n) f

let veq_eq_t_list (pre_n post_n : nat) = Ll.vec post_n (option (Fin.fin pre_n))

[@@__vequiv__]
let veq_to_list (#pre_n #post_n : nat) (f : veq_eq_t pre_n post_n) : veq_eq_t_list pre_n post_n =
  Ll.initi 0 post_n f

[@@__vequiv__]
noextract
let veq_of_list (#pre_n #post_n : nat) (l : veq_eq_t_list pre_n post_n) : veq_eq_t pre_n post_n =
  FExt.on (Fin.fin post_n) (L.index l)

let veq_of_to_list #pre_n #post_n (f : veq_eq_t pre_n post_n)
  : Lemma (veq_of_list (veq_to_list f) == f)
          [SMTPat (veq_of_list (veq_to_list f))]
  = FExt.extensionality _ _ (veq_of_list (veq_to_list f)) f

let veq_to_of_list #pre_n #post_n (l : veq_eq_t_list pre_n post_n)
  : Lemma (veq_to_list (veq_of_list l) == l)
          [SMTPat (veq_to_list (veq_of_list l))]
  = Ll.list_extensionality (veq_to_list (veq_of_list l)) l (fun _ -> ())

[@@__vequiv__]
let veq_list_eq (#pre_n #post_n : nat) : U.eq_dec (veq_eq_t_list pre_n post_n)
  = Ll.list_eq (Learn.Option.opt_eq (fun x y -> x = y))

// We only requires the equality of the types, we could require the equality of the vprop' ?
let veq_typ_eq (pre post : Fl.ty_list) (f_eq : veq_eq_t (L.length pre) (L.length post))
  : prop
  = forall (i : Fin.fin (L.length post) {Some? (f_eq i)}) . L.index post i == L.index pre (Some?.v (f_eq i))

let elim_veq_typ_eq (#pre #post : Fl.ty_list) (#f_eq : veq_eq_t (L.length pre) (L.length post))
                    ($h : squash (veq_typ_eq pre post f_eq)) (i : Fin.fin (L.length post))
  : Lemma (requires Some? (f_eq i))
          (ensures  L.index post i == L.index pre (Some?.v (f_eq i)))
  = ()

let veq_sel_eq (#pre #post : Fl.ty_list) (f_eq : veq_eq_t (L.length pre) (L.length post))
               (sl0 : Fl.flist pre) (sl1 : Fl.flist post)
  : prop
  = forall (i : Fin.fin (L.length post) {Some? (f_eq i)}) . sl1 i === sl0 (Some?.v (f_eq i))

/// [veq_sel_eq] written with a conjunction instead of a forall
// TODO take a [veq_eq_t_list] as argument
let rec veq_sel_eq_eff_aux (#pre #post : Fl.ty_list) (f_eq : veq_eq_t (L.length pre) (L.length post))
                           (sl0 : Fl.flist pre) (sl1 : Fl.flist post) (i : nat)
  : Pure prop (requires veq_typ_eq pre post f_eq) (ensures fun _ -> True) (decreases L.length post - i)
  = if i >= L.length post then True
    else match f_eq i with
    | None   -> veq_sel_eq_eff_aux f_eq sl0 sl1 (i+1)
    | Some j -> sl1 i == U.cast _ (sl0 j) /\ veq_sel_eq_eff_aux f_eq sl0 sl1 (i+1)

let veq_sel_eq_eff (#pre #post : Fl.ty_list) (f_eq : veq_eq_t (L.length pre) (L.length post))
                   (sl0 : Fl.flist pre) (sl1 : Fl.flist post)
  : Pure prop (requires veq_typ_eq pre post f_eq) (ensures fun _ -> True)
  = veq_sel_eq_eff_aux f_eq sl0 sl1 0

val veq_sel_eq_eff_sound
      (#pre #post : Fl.ty_list) (f_eq : veq_eq_t (L.length pre) (L.length post))
      (sl0 : Fl.flist pre) (sl1 : Fl.flist post)
  : Lemma (requires veq_typ_eq pre post f_eq)
          (ensures  veq_sel_eq_eff f_eq sl0 sl1 <==> veq_sel_eq f_eq sl0 sl1)


let veq_partial_eq (#pre #post : Fl.ty_list) (l_eq : veq_eq_t_list (L.length pre) (L.length post))
                   (sl0 : Fl.flist pre)
  : Pure (Fl.partial_eq_t post)
         (requires veq_typ_eq pre post (veq_of_list l_eq))
         (ensures  fun _ -> True)
  = Dl.initi_ty (L.map option post) (fun i ->
       match L.index l_eq i returns option (L.index post i) with
       | None   -> None
       | Some j -> Some (U.cast _ (sl0 j)))

val veq_sel_eq_iff_partial_eq
      (#pre #post : Fl.ty_list) (l_eq : veq_eq_t_list (L.length pre) (L.length post))
      (sl0 : Fl.flist pre) (sl1 : Fl.flist post)
  : Lemma (requires veq_typ_eq pre post (veq_of_list l_eq))
          (ensures  veq_sel_eq (veq_of_list l_eq) sl0 sl1 <==> Fl.partial_eq sl1 (veq_partial_eq l_eq sl0))

// Should we allow post to depend on some returned variables ? It could be useful to destruct [vdep]
[@@__vequiv__]
noeq
type vequiv (pre post : vprop_list) = {
  veq_req : sl_f pre -> Type0;
  veq_ens : sl_f pre -> sl_f post -> Type0;
  veq_eq  : veq_eq_t_list (L.length pre) (L.length post);
  veq_typ : squash (veq_typ_eq (vprop_list_sels_t pre) (vprop_list_sels_t post) (veq_eq_sl (veq_of_list veq_eq)));
  veq_g   : (opened : Mem.inames) ->
            SteelGhost unit opened
              (vprop_of_list pre) (fun () -> vprop_of_list post)
              (requires fun h0 -> veq_req (sel pre h0))
              (ensures  fun h0 () h1 -> veq_ens (sel pre h0) (sel post h1) /\
                                     veq_sel_eq (veq_eq_sl (veq_of_list veq_eq)) (sel pre h0) (sel post h1))
}

[@@__vequiv__]
let veq_ens1 (#pre #post : vprop_list) (veq : vequiv pre post) (sl0 : sl_f pre) (sl1 : sl_f post) : prop
  = veq.veq_ens sl0 sl1 /\ veq_sel_eq (veq_eq_sl (veq_of_list veq.veq_eq)) sl0 sl1

[@@__vequiv__]
let veq_f (#pre #post : vprop_list) (veq : vequiv pre post) : veq_eq_t (L.length pre) (L.length post)
  = veq_of_list veq.veq_eq

[@@__vequiv__]
let vequiv_refl (v : vprop_list) : vequiv v v = {
  veq_req = (fun _ -> True);
  veq_ens = (fun _ _ -> True);
  veq_eq  = Ll.initi 0 (L.length v) (fun i -> Some (i <: Fin.fin (L.length v)));
  veq_typ = ();
  veq_g   = (fun opened -> noop ())
}

(****** [vequiv_trans] *)

[@@__vequiv__]
let vequiv_trans_req (#v0 #v1 #v2 : vprop_list) (e0 : vequiv v0 v1) (e1 : vequiv v1 v2)
                     (sl0 : sl_f v0) : Type0
  = e0.veq_req sl0 /\
    Fl.forall_flist_part (vprop_list_sels_t v1) (veq_partial_eq e0.veq_eq sl0) (fun (sl1 : sl_f v1) ->
      e0.veq_ens sl0 sl1 ==> e1.veq_req sl1)

/// We need to enforce in [veq_ens] the equalities of [e1] that are not propagated by [e0].
[@@__vequiv__]
let vequiv_trans_eq1_restr_f (#v0 #v1 : vprop_list) (e0 : vequiv v0 v1)
      (o : option (Fin.fin (L.length v1))) : option (Fin.fin (L.length v1))
  = match o with
  | Some j -> if None? (L.index e0.veq_eq j) then Some j else None
  | None -> None

[@@__vequiv__]
let vequiv_trans_eq1_restr (#v0 #v1 #v2 : vprop_list) (e0 : vequiv v0 v1) (e1 : vequiv v1 v2)
  : veq_eq_t_list (L.length v1) (L.length v2)
  = L.map (vequiv_trans_eq1_restr_f e0) e1.veq_eq

val vequiv_trans_eq1_restr_typ (#v0 #v1 #v2 : vprop_list) (e0 : vequiv v0 v1) (e1 : vequiv v1 v2)
  : Lemma (requires veq_typ_eq (vprop_list_sels_t v1) (vprop_list_sels_t v2) (veq_eq_sl (veq_f e1)))
          (ensures  veq_typ_eq (vprop_list_sels_t v1) (vprop_list_sels_t v2)
                          (veq_eq_sl (veq_of_list (vequiv_trans_eq1_restr e0 e1))))

[@@__vequiv__]
let vequiv_trans_ens (#v0 #v1 #v2 : vprop_list) (e0 : vequiv v0 v1) (e1 : vequiv v1 v2)
                     (sl0 : sl_f v0) (sl2 : sl_f v2) : Type0
  = Fl.exists_flist_part (vprop_list_sels_t v1) (veq_partial_eq e0.veq_eq sl0) (fun (sl1 : sl_f v1) ->
      e0.veq_ens sl0 sl1 /\ e1.veq_ens sl1 sl2 /\
      (e1.veq_typ; vequiv_trans_eq1_restr_typ e0 e1;
       veq_sel_eq_eff (veq_eq_sl (veq_of_list (vequiv_trans_eq1_restr e0 e1))) sl1 sl2))

val vequiv_trans_req_iff (#v0 #v1 #v2 : vprop_list) (e0 : vequiv v0 v1) (e1 : vequiv v1 v2)
                         (sl0 : sl_f v0)
  : Lemma (vequiv_trans_req e0 e1 sl0 <==>
            (e0.veq_req sl0 /\ (forall (sl1 : sl_f v1) . veq_ens1 e0 sl0 sl1 ==> e1.veq_req sl1)))

val vequiv_trans_ens_imp (#v0 #v1 #v2 : vprop_list) (e0 : vequiv v0 v1) (e1 : vequiv v1 v2)
                         (sl0 : sl_f v0) (sl2 : sl_f v2)
  : Lemma ((exists (sl1 : sl_f v1) . veq_ens1 e0 sl0 sl1 /\ veq_ens1 e1 sl1 sl2)
            ==> vequiv_trans_ens e0 e1 sl0 sl2)

[@@__vequiv__]
let vequiv_trans (#v0 #v1 #v2 : vprop_list) (e0 : vequiv v0 v1) (e1 : vequiv v1 v2) : vequiv v0 v2 = {
  veq_req = vequiv_trans_req e0 e1;
  veq_ens = vequiv_trans_ens e0 e1;
  veq_eq  = veq_to_list (mk_veq_eq (L.length v0) (L.length v2)
                      (fun i2 -> Opt.bind (veq_of_list e1.veq_eq i2) (veq_of_list e0.veq_eq)));
  veq_typ = ();
  veq_g   = (FStar.Classical.forall_intro   (vequiv_trans_req_iff e0 e1);
             FStar.Classical.forall_intro_2 (vequiv_trans_ens_imp e0 e1);
            (fun opened -> e0.veq_g opened; e1.veq_g opened))
}


(****** [vequiv_cons] *)

[@@__vequiv__]
let fin_shift (l m : nat) (n : nat {l + m <= n}) (i : Fin.fin l) : Fin.fin n
  = i + m

[@@__vequiv__]
let vequiv_cons_eq #pre_n #post_n (e : veq_eq_t_list pre_n post_n)
  : veq_eq_t_list (pre_n+1) (post_n+1)
  = Some 0 :: L.map (Opt.map (fin_shift pre_n 1 (pre_n+1))) e

val vequiv_cons_typ (hd : Type) (#pre #post : Fl.ty_list) (e : veq_eq_t_list (L.length pre) (L.length post))
  : Lemma (requires veq_typ_eq pre post (veq_of_list e))
          (ensures  veq_typ_eq (hd :: pre) (hd :: post) (U.cast _ (veq_of_list (vequiv_cons_eq e))))

val vequiv_cons_g (hd : SE.vprop') (#pre #post : vprop_list) (e : vequiv pre post) (opened : Mem.inames)
  : SteelGhost unit opened (vprop_of_list (hd :: pre)) (fun () -> vprop_of_list (hd :: post))
      (requires fun h0       -> e.veq_req (Fl.tail #hd.t #(vprop_list_sels_t  pre) (sel (hd :: pre) h0)))
      (ensures  fun h0 () h1 -> let sl0 = sel (hd :: pre) h0 in
                             let sl1 = sel (hd :: post) h1 in
                             e.veq_ens (Fl.tail #hd.t #(vprop_list_sels_t  pre) sl0)
                                       (Fl.tail #hd.t #(vprop_list_sels_t post) sl1) /\
                             veq_sel_eq (U.cast _ (veq_of_list (vequiv_cons_eq e.veq_eq))) sl0 sl1)

[@@__vequiv__]
let vequiv_cons (hd : SE.vprop') (#pre #post : vprop_list) (e : vequiv pre post)
  : vequiv (hd :: pre) (hd :: post)
  = {
    veq_req = (fun sl0     -> e.veq_req (Fl.tail #hd.t #(vprop_list_sels_t  pre) sl0));
    veq_ens = (fun sl0 sl1 -> e.veq_ens (Fl.tail #hd.t #(vprop_list_sels_t  pre) sl0)
                                     (Fl.tail #hd.t #(vprop_list_sels_t post) sl1));
    veq_eq  = vequiv_cons_eq e.veq_eq;
    veq_typ = (e.veq_typ;
               vequiv_cons_typ hd.t #(vprop_list_sels_t pre) #(vprop_list_sels_t post) e.veq_eq;
               ());
    veq_g   = vequiv_cons_g hd e
   }


(****** [vequiv_app] *)

[@@__vequiv__]
let vequiv_app_eq
      #pre0_n #post0_n (e0 : veq_eq_t_list pre0_n post0_n)
      #pre1_n #post1_n (e1 : veq_eq_t_list pre1_n post1_n)
  : veq_eq_t_list (pre0_n+pre1_n) (post0_n+post1_n)
  = L.(map (Opt.map (fin_shift pre0_n   0    (pre0_n + pre1_n))) e0
     @ map (Opt.map (fin_shift pre1_n pre0_n (pre0_n + pre1_n))) e1)

val vequiv_app_typ
      (#pre0 #post0 : Fl.ty_list) (e0 : veq_eq_t_list (L.length pre0) (L.length post0))
      (#pre1 #post1 : Fl.ty_list) (e1 : veq_eq_t_list (L.length pre1) (L.length post1))
  : Lemma (requires veq_typ_eq pre0 post0 (veq_of_list e0) /\
                    veq_typ_eq pre1 post1 (veq_of_list e1))
          (ensures  veq_typ_eq L.(pre0 @ pre1) L.(post0 @ post1)
                                 (U.cast _ (veq_of_list (vequiv_app_eq e0 e1))))

val vequiv_app_sl_eq
      (#pre0 #post0 : Fl.ty_list) (e0 : veq_eq_t_list (L.length pre0) (L.length post0))
      (#pre1 #post1 : Fl.ty_list) (e1 : veq_eq_t_list (L.length pre1) (L.length post1))
      (sl0_0 : Fl.flist pre0)  (sl0_1 : Fl.flist pre1)
      (sl1_0 : Fl.flist post0) (sl1_1 : Fl.flist post1)
  : Lemma (requires veq_sel_eq (veq_of_list e0) sl0_0 sl1_0 /\
                    veq_sel_eq (veq_of_list e1) sl0_1 sl1_1)
          (ensures  veq_sel_eq (U.cast _ (veq_of_list (vequiv_app_eq e0 e1)))
                                 (Fl.append sl0_0 sl0_1) (Fl.append sl1_0 sl1_1))
val vequiv_app_g
      (#pre0 #post0 : vprop_list) (e0 : vequiv pre0 post0)
      (#pre1 #post1 : vprop_list) (e1 : vequiv pre1 post1)
      (opened : Mem.inames)
  : SteelGhost unit opened (vprop_of_list L.(pre0 @ pre1)) (fun () -> vprop_of_list L.(post0 @ post1))
      (requires fun h0       -> let sl0s = split_vars pre0 pre1 (sel L.(pre0 @ pre1) h0) in
                             e0.veq_req sl0s._1 /\ e1.veq_req sl0s._2)
      (ensures  fun h0 () h1 -> let sl0  = sel L.(pre0  @ pre1 ) h0   in
                             let sl1  = sel L.(post0 @ post1) h1   in
                             let sl0s = split_vars pre0  pre1  sl0 in
                             let sl1s = split_vars post0 post1 sl1 in
                             e0.veq_ens sl0s._1 sl1s._1 /\ e1.veq_ens sl0s._2 sl1s._2 /\
                             veq_sel_eq (U.cast _ (veq_of_list (vequiv_app_eq e0.veq_eq e1.veq_eq))) sl0 sl1)

[@@__vequiv__]
let vequiv_app
      (#pre0 #post0 : vprop_list) (e0 : vequiv pre0 post0)
      (#pre1 #post1 : vprop_list) (e1 : vequiv pre1 post1)
  : vequiv L.(pre0 @ pre1) L.(post0 @ post1)
  = {
    veq_req = (fun sl0     -> let sl0s = split_vars pre0 pre1 sl0 in
                           e0.veq_req sl0s._1 /\ e1.veq_req sl0s._2);
    veq_ens = (fun sl0 sl1 -> let sl0s = split_vars pre0  pre1  sl0 in
                           let sl1s = split_vars post0 post1 sl1 in
                           e0.veq_ens sl0s._1 sl1s._1 /\ e1.veq_ens sl0s._2 sl1s._2);
    veq_eq  = vequiv_app_eq e0.veq_eq e1.veq_eq;
    veq_typ = (e0.veq_typ; e1.veq_typ;
               vequiv_app_typ #(vprop_list_sels_t pre0) #(vprop_list_sels_t post0) e0.veq_eq
                              #(vprop_list_sels_t pre1) #(vprop_list_sels_t post1) e1.veq_eq;
               Ll.map_append SE.Mkvprop'?.t pre0 pre1;
               Ll.map_append SE.Mkvprop'?.t post0 post1;
               ());
    veq_g   = vequiv_app_g e0 e1
   }


(***** [vequiv_perm] *)

let vequiv_perm : vprop_list -> vprop_list -> Type = Perm.pequiv #vprop'

unfold
let vequiv_sl (#vs0 #vs1 : vprop_list) (f : vequiv_perm vs0 vs1)
  : Perm.pequiv (vprop_list_sels_t vs0) (vprop_list_sels_t vs1)
  = Perm.map_apply_r f Mkvprop'?.t vs0;
    U.cast #(Perm.perm_f (L.length vs0)) (Perm.perm_f (L.length (vprop_list_sels_t vs0))) f    

unfold
let extract_vars (#src #dst : vprop_list)
                 (p : vequiv_perm src dst)
                 (xs : sl_f src)
  : sl_f dst
  =
    Fl.apply_pequiv (vequiv_sl p) xs

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
    Fl.apply_pequiv_sym_l (vequiv_sl f) xs

/// applying a permutation on the context's vprop

val steel_change_perm (#vs0 #vs1 : vprop_list) (#opened:Mem.inames) (f : vequiv_perm vs0 vs1)
  : SteelGhost unit opened (vprop_of_list vs0) (fun () -> vprop_of_list vs1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel_f vs1 h1 == extract_vars f (sel_f vs0 h0))

[@@__vequiv__]
let vequiv_of_perm_eq (#pre #post : vprop_list) (f : vequiv_perm pre post)
  : veq_eq_t (L.length pre) (L.length post)
  = mk_veq_eq (L.length pre) (L.length post) (fun i -> Some (f i))

val vequiv_of_perm_g (#pre #post : vprop_list) (f : vequiv_perm pre post) (opened : Mem.inames)
  : SteelGhost unit opened (vprop_of_list pre) (fun () -> vprop_of_list post)
      (requires fun _ -> True)
      (ensures  fun h0 () h1 -> veq_sel_eq (veq_eq_sl (vequiv_of_perm_eq f)) (sel pre h0) (sel post h1))

[@@__vequiv__]
let vequiv_of_perm (#pre #post : vprop_list) (f : vequiv_perm pre post) : vequiv pre post = {
  veq_req = (fun (_ : sl_f pre) -> True);
  veq_ens = (fun (_ : sl_f pre) (_ : sl_f post) -> True);
  veq_eq  = veq_to_list (vequiv_of_perm_eq f);
  veq_typ = ();
  veq_g   = vequiv_of_perm_g f
}


(*** [repr_steel_t] *)

type pre_t = vprop_list
type post_t (a : Type) = a -> vprop_list

type req_t (pre : pre_t) = sl_f pre -> Type0
type ens_t (pre : pre_t) (a : Type) (post : post_t a) = sl_f pre -> (x : a) -> sl_f (post x) -> Type0

type repr_steel_t (ek : SH.effect_kind) (a : Type)
       (pre : pre_t) (post : post_t a)
       (req : req_t pre) (ens : ens_t pre a post)
  = SH.steel a
      (vprop_of_list pre) (fun x -> vprop_of_list (post x))
      (requires fun h0 -> req (sel pre h0)) (ensures fun h0 x h1 -> ens (sel pre h0) x (sel_f (post x) h1))
      ek

// FIXME: this definition fails when loaded as a dependency but not when lax-checked
inline_for_extraction noextract
let repr_steel_subcomp
      (#a : Type) (#pre : pre_t) (#post : post_t a)
      (req_f : req_t pre) (ens_f : ens_t pre a post)
      (req_g : req_t pre) (ens_g : ens_t pre a post)
      (pf_req : (sl0 : sl_f pre) ->
                Lemma (requires req_g sl0) (ensures req_f sl0))
      (pf_ens : (sl0 : sl_f pre) -> (x : a) -> (sl1 : sl_f (post x)) ->
                Lemma (requires req_f sl0 /\ req_g sl0 /\ ens_f sl0 x sl1) (ensures ens_g sl0 x sl1))
      (r : repr_steel_t SH.KSteel a pre post req_f ens_f)
  : repr_steel_t SH.KSteel a pre post req_g ens_g
  = SH.steel_f (fun () ->
      (**) let sl0 : Ghost.erased (t_of (vprop_of_list pre)) = gget (vprop_of_list pre) in
      (**) pf_req (vpl_sels_f pre sl0);
      let x = SH.steel_u r () in
      (**) let sl1 : Ghost.erased (t_of (vprop_of_list (post x))) = gget (vprop_of_list (post x)) in
      (**) pf_ens (vpl_sels_f pre sl0) x (vpl_sels_f (post x) sl1);
      Steel.Effect.Atomic.return x)

(*// This fail, seemingly because of the expansion of the memories when checking the post
[@@ handle_smt_goals ]
let tac () = dump "SMT query"
let steel_of_repr
      (#a : Type) (#pre : pre_t) (#post : post_t a) (#req : req_t pre) (#ens : ens_t pre a post)
      (f : unit_steel a pre post req ens)
  : Steel a pre post req ens
  = f ()*)

[@@ Learn.Tactics.Util.__tac_helper__]
noeq
type to_repr_t (a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
= {
  r_pre  : pre_t;
  r_post : post_t a;
  r_req  : req_t r_pre;
  r_ens  : ens_t r_pre a r_post;
  r_pre_eq  : unit -> Lemma (pre `equiv` vprop_of_list r_pre);
  r_post_eq : (x : a) -> Lemma (post x `equiv` vprop_of_list (r_post x));
  r_req_eq  : (h0 : rmem pre) -> Lemma (req h0 ==
                  r_req (sel r_pre (
                          r_pre_eq ();
                          equiv_can_be_split pre (vprop_of_list r_pre);
                          focus_rmem h0 (vprop_of_list r_pre))));
  r_ens_eq  : (h0 : rmem pre) -> (x : a) -> (h1 : rmem (post x)) -> Lemma (ens h0 x h1 ==
                  r_ens (sel r_pre (
                          r_pre_eq ();
                          equiv_can_be_split pre (vprop_of_list r_pre);
                          focus_rmem h0 (vprop_of_list r_pre)))
                        x
                        (sel (r_post x) (
                          r_post_eq x;
                          equiv_can_be_split (post x) (vprop_of_list (r_post x));
                          focus_rmem h1 (vprop_of_list (r_post x)))))
}

inline_for_extraction noextract
val steel_of_repr
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      (f : repr_steel_t SH.KSteel a tr.r_pre tr.r_post tr.r_req tr.r_ens)
  : SH.unit_steel a pre post req ens

inline_for_extraction noextract
val repr_steel_of_steel
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      ($f  : SH.unit_steel a pre post req ens)
  : repr_steel_t SH.KSteel a tr.r_pre tr.r_post tr.r_req tr.r_ens 

inline_for_extraction noextract
val steel_ghost_of_repr
      (#a : Type) (#opened : Mem.inames)
      (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      (f : repr_steel_t (SH.KGhost opened) a tr.r_pre tr.r_post tr.r_req tr.r_ens)
  : SH.unit_steel_ghost a opened pre post req ens

inline_for_extraction noextract
val repr_steel_of_steel_ghost
      (#a : Type) (#opened : Mem.inames)
      (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      ($f  : SH.unit_steel_ghost a opened pre post req ens)
  : repr_steel_t (SH.KGhost opened) a tr.r_pre tr.r_post tr.r_req tr.r_ens


(*** [prog_tree] *)

noeq
type prog_tree : (a : Type u#a) -> Type u#(max (a+1) 2) =
  // A specification of the subprogram, used to represent function calls
  | Tspec  : (a : Type u#a) -> (pre : pre_t) -> (post : post_t a) ->
             (req : req_t pre) -> (ens : ens_t pre a post) ->
             prog_tree a
  // A Steel specification, used to represent calls to Steel functions
  | TspecS : (a : Type u#a) -> (pre : SE.pre_t) -> (post : SE.post_t a) ->
             (req : SE.req_t pre) -> (ens : SE.ens_t pre a post) ->
             prog_tree a
  // return, with a hint for introducing dependencies in the returned value
  | Tret   : (a : Type u#a) -> (x : a) -> (sl_hint : post_t a) ->
             prog_tree a
  // bind
  | Tbind  : (a : Type u#a) -> (b : Type u#a) ->
             (f : prog_tree a) -> (g : a -> prog_tree b) ->
             prog_tree b
  // bind pure, models a polymonadic bind between PURE and our monad
  | TbindP : (a : Type u#a) -> (b : Type u#a) ->
             (wp : pure_wp a) -> (g : a -> prog_tree b) ->
             prog_tree b
  // if-then-else
  | Tif    : (a : Type u#a) -> (guard : bool) ->
             (thn : prog_tree a) -> (els : prog_tree a) ->
             prog_tree a


(*** slprop unification conditions *)

(* TODO:
   - ? equalities vs vequiv
      + Tspec : post x == post' x @ frame, allow shuffle at the end
   - ~pr ! allow assumptions -> VC
   - ALT: recursively defined type *)

[@@ Learn.Tactics.Util.__tac_helper__]
noeq
type tree_cond_Spec (a : Type) (pre : pre_t) (post : post_t a) = {
  tcs_pre     : pre_t;
  tcs_post    : post_t a;
  tcs_frame   : vprop_list;
  tcs_pre_eq  : vequiv tcs_pre L.(pre @ tcs_frame);
  tcs_post_eq : (x : a) -> vequiv L.(post x @ tcs_frame) (tcs_post x)
}

noeq
type tree_cond : (#a : Type u#a) -> (t : prog_tree a) -> (pre : pre_t) -> (post : post_t a) -> Type u#(max (a+1) 2) =
  | TCspec  : (#a : Type u#a) -> (#pre : pre_t) -> (#post : post_t a) ->
              (#req : req_t pre) -> (#ens : ens_t pre a post) ->
              (tcs : tree_cond_Spec a pre post) ->
              tree_cond (Tspec a pre post req ens) tcs.tcs_pre tcs.tcs_post
  | TCspecS : (#a : Type u#a) -> (#pre : SE.pre_t) -> (#post : SE.post_t a) ->
              (#req : SE.req_t pre) -> (#ens : SE.ens_t pre a post) ->
              (tr  : to_repr_t a pre post req ens) ->
              (tcs : tree_cond_Spec a tr.r_pre tr.r_post) ->
              tree_cond (TspecS a pre post req ens) tcs.tcs_pre tcs.tcs_post
  | TCret   : (#a : Type u#a) -> (#x : a) -> (#sl_hint : post_t a) ->
              (pre : pre_t) -> (post : post_t a) ->
              (p : vequiv pre (post x)) ->
              tree_cond (Tret a x sl_hint) pre post
  | TCbind  : (#a : Type u#a) -> (#b : Type u#a) -> (#f : prog_tree a) -> (#g : (a -> prog_tree b)) ->
              (pre : pre_t) -> (itm : post_t a) -> (post : post_t b) ->
              (cf : tree_cond f pre itm) -> (cg : ((x : a) -> tree_cond (g x) (itm x) post)) ->
              tree_cond (Tbind a b f g) pre post
  | TCbindP : (#a : Type u#a) -> (#b : Type u#a) ->
              (#wp : pure_wp a) -> (#g : (a -> prog_tree b)) ->
              (pre : pre_t) -> (post : post_t b) ->
              (cg : ((x : a) -> tree_cond (g x) pre post)) ->
              tree_cond (TbindP a b wp g) pre post
  | TCif    : (#a : Type u#a) -> (#guard : bool) -> (#thn : prog_tree a) -> (#els : prog_tree a) ->
              (pre : pre_t) -> (post : post_t a) ->
              (cthn : tree_cond thn pre post) -> (cels : tree_cond els pre post) ->
              tree_cond (Tif a guard thn els) pre post

(**** Shape *)

noeq
type shape_tree : (pre_n : nat) -> (post_n : nat) -> Type =
  | Sspec  : (pre_n : nat) -> (post_n : nat) -> (pre'_n : nat) -> (post'_n : nat) -> (frame_n : nat) ->
             (e0 : veq_eq_t_list pre'_n (pre_n + frame_n)) ->
             (e1 : veq_eq_t_list (post_n + frame_n) post'_n) ->
             shape_tree pre'_n post'_n
  | Sret   : (pre_n : nat) -> (post_n : nat) ->
             (e : veq_eq_t_list pre_n post_n) ->
             shape_tree pre_n post_n
  | Sbind  : (pre_n : nat) -> (itm_n : nat) -> (post_n : nat) ->
             (f : shape_tree pre_n itm_n) -> (g : shape_tree itm_n post_n) ->
             shape_tree pre_n post_n
  | SbindP : (pre_n : nat) -> (post_n : nat) ->
             (g : shape_tree pre_n post_n) ->
             shape_tree pre_n post_n
  | Sif    : (pre_n : nat) -> (post_n : nat) ->
             (thn : shape_tree pre_n post_n) -> (els : shape_tree pre_n post_n) ->
             shape_tree pre_n post_n

unfold
let tree_cond_has_shape_Spec
      (a : Type) (pre : pre_t) (post : post_t a) (tcs : tree_cond_Spec a pre post)
      (#post_n : nat) (s : shape_tree (L.length tcs.tcs_pre) post_n)
  : prop
  = match s with
  | Sspec pre_n post_n pre'_n post'_n frame_n e0' e1' ->
    pre_n   = L.length pre /\
    pre'_n  = L.length tcs.tcs_pre /\
    frame_n = L.length tcs.tcs_frame /\
    tcs.tcs_pre_eq.veq_eq `veq_list_eq` e0' /\
   (forall (x : a) .
     L.length (post  x) = post_n /\
     L.length (tcs.tcs_post x) = post'_n /\
     (tcs.tcs_post_eq x).veq_eq `veq_list_eq` e1')
  | _ -> False

[@@ strict_on_arguments [4;6]] (* strict on c;s *)
let rec tree_cond_has_shape
      (#a : Type) (#pre : pre_t) (#post0 : post_t a) (#t : prog_tree a)
      (c : tree_cond t pre post0)
      (#post_n : nat) (s : shape_tree (L.length pre) post_n)
  : Pure prop (requires True) (ensures fun p -> p ==> (forall (x : a) . L.length (post0 x) = post_n)) (decreases c)
  = match c with
  | TCspec #a #pre #post tcs -> tree_cond_has_shape_Spec a pre post tcs s
  | TCspecS #a tr tcs -> tree_cond_has_shape_Spec a tr.r_pre tr.r_post tcs s
  | TCret #a pre post e ->
      (match s with
      | Sret pre_n post_n e' ->
        pre_n = L.length pre /\
       (forall (x : a) . L.length (post x) = post_n) /\
        e.veq_eq `veq_list_eq` e'
      | _ -> False)
  | TCbind #a #b pre itm post f g ->
      (match s with
      | Sbind _ itm_n post_n s_f s_g ->
        tree_cond_has_shape f s_f /\
       (forall (x : a) . tree_cond_has_shape (g x) s_g) /\
       (forall (y : b) . L.length (post y) = post_n)
      | _ -> False)
  | TCbindP #a #b pre post g ->
      (match s with
      | SbindP _ post_n s_g ->
        (forall (x : a) . tree_cond_has_shape (g x) s_g) /\
        (forall (y : b) . L.length (post y) = post_n)
      | _ -> False)
  | TCif #a pre post thn els ->
      (match s with
      | Sif _ _ s_thn s_els ->
        tree_cond_has_shape thn s_thn /\
        tree_cond_has_shape els s_els
      | _ -> False)

noeq inline_for_extraction noextract
type prog_cond (#a : Type) (t : prog_tree a) (pre : pre_t) (post : post_t a) = {
  pc_tree     : tree_cond t pre post;
  pc_post_len : nat;
  pc_shape    : (s : shape_tree (L.length pre) pc_post_len {tree_cond_has_shape pc_tree s})
}


(**** requires / ensures *)

(** spec *)

// ALT? directly express with a bind

let spec_req (#a : Type) (#pre : pre_t) (#post : post_t a) (tcs : tree_cond_Spec a pre post)
             (req : req_t pre) (ens : ens_t pre a post)
  : req_t tcs.tcs_pre
  = fun sl0 ->
      tcs.tcs_pre_eq.veq_req sl0 /\
     (forall (sl0' : sl_f pre) (sl_frame : sl_f tcs.tcs_frame) .
      veq_ens1 tcs.tcs_pre_eq sl0 (append_vars sl0' sl_frame) ==>
     (req sl0' /\
     (forall (x : a) (sl1' : sl_f (post x)) . ens sl0' x sl1' ==>
      (tcs.tcs_post_eq x).veq_req (append_vars sl1' sl_frame))))

let spec_ens (#a : Type) (#pre : pre_t) (#post : post_t a) (tcs : tree_cond_Spec a pre post)
             (ens : ens_t pre a post)
  : ens_t tcs.tcs_pre a tcs.tcs_post
  = fun sl0 x sl1 -> exists (sl0' : sl_f pre) (sl1' : sl_f (post x)) (sl_frame : sl_f tcs.tcs_frame) .
      veq_ens1 tcs.tcs_pre_eq sl0 (append_vars sl0' sl_frame) /\
      ens sl0' x sl1' /\
      veq_ens1 (tcs.tcs_post_eq x) (append_vars sl1' sl_frame) sl1

(** return *)

let return_req (#pre : pre_t) (#post : vprop_list) (veq : vequiv pre post) : req_t pre
  = veq.veq_req

let return_ens (#a : Type) (x : a) (#pre : pre_t) (#post : post_t a) (e : vequiv pre (post x))
  : ens_t pre a post
  = fun sl0 r sl1 ->
      r == x /\ veq_ens1 e sl0 sl1

(** bind *)

let bind_req (#a : Type)
      (#pre : pre_t) (#itm : post_t a)
      (req_f : req_t pre) (ens_f : ens_t pre a itm)
      (req_g : (x:a) -> req_t (itm x))
  : req_t pre
  = fun sl0 -> req_f sl0 /\
      (forall (x : a) (sl1 : sl_f (itm x)) .
        ens_f sl0 x sl1 ==> req_g x sl1)

/// Unlike the bind combiner of Steel, our ensures clause does not recall the pre-condition of [f] for
/// the reason explained on [Experiment.Repr.Fun.tree_ens]

let bind_ens (#a : Type) (#b : Type)
      (#pre : pre_t) (#itm : post_t a) (#post : post_t b)
      (ens_f : ens_t pre a itm) (ens_g : (x:a) -> ens_t (itm x) b post)
  : ens_t pre b post
  = fun sl0 y sl2 ->
      (exists (x : a) (sl1 : sl_f (itm x)) .
        ens_f sl0 x sl1 /\
        ens_g x sl1 y sl2)

(** bind_pure *)

let bind_pure_req (#a : Type) (wp : pure_wp a)
      (#pre : pre_t)
      (req : a -> req_t pre)
  : req_t pre
  = fun sl0 -> wp (fun x -> req x sl0)

let bind_pure_ens (#a : Type) (#b : Type)
      (wp : pure_wp a)
      (#pre : pre_t) (#post : post_t b)
      (ens : a -> ens_t pre b post)
  : ens_t pre b post
  = fun sl0 y sl1 -> (exists (x:a) . as_ensures wp x /\ ens x sl0 y sl1)

(** if-then-else *)

let ite_req (#a : Type) (guard : bool) (#pre : pre_t)
      (req_thn : req_t pre) (req_els : req_t pre)
  : req_t pre
  = fun sl0 -> if guard then req_thn sl0 else req_els sl0

let ite_ens (#a : Type) (guard : bool) (#pre : pre_t) (#post : post_t a)
      (ens_thn : ens_t pre a post) (ens_els : ens_t pre a post)
  : ens_t pre a post
  = fun sl0 x sl1 -> if guard then ens_thn sl0 x sl1 else ens_els sl0 x sl1


(** prog_tree *)

[@@ strict_on_arguments [4]] (* strict on c *)
let rec tree_req (#a : Type u#a) (t : prog_tree a)
                 (#pre : pre_t) (#post : post_t a) (c : tree_cond t pre post)
                 (sl0 : sl_f pre)
  : Tot Type0 (decreases t) =
  match c with
  | TCspec #_ #pre #_ #req #ens  tcs ->
             spec_req tcs req ens sl0
  | TCspecS #_ tr tcs ->
             spec_req tcs tr.r_req tr.r_ens sl0
  | TCret #_ #_  _ _  e ->
             return_req e sl0
  | TCbind #_ #_ #f #g  pre itm _  cf cg ->
             bind_req (tree_req f cf) (tree_ens f cf) (fun x -> tree_req (g x) (cg x)) sl0
  | TCbindP #_ #_ #wp #g  pre _  cg ->
             bind_pure_req wp (fun x -> tree_req (g x) (cg x)) sl0
  | TCif #a #guard  pre _ thn els ->
             ite_req #a guard (tree_req _ thn) (tree_req _ els) sl0

and tree_ens (#a : Type u#a) (t : prog_tree a)
             (#pre : pre_t) (#post : post_t a) (c : tree_cond t pre post)
             (sl0 : sl_f pre) (res : a) (sl1 : sl_f (post res))
  : Tot Type0 (decreases t) =
  match c with
  | TCspec #a #pre #post #_ #ens  tcs ->
             spec_ens tcs ens sl0 res sl1
  | TCspecS #_ tr tcs ->
             spec_ens tcs tr.r_ens sl0 res sl1
  | TCret #a #x  _ _  e ->
             return_ens x e sl0 res sl1
  | TCbind #_ #_ #f #g  pre itm post  cf cg ->
             bind_ens (tree_ens f cf) (fun x -> tree_ens (g x) (cg x)) sl0 res sl1
  | TCbindP #_ #_ #wp #g  pre post  cg ->
             bind_pure_ens wp (fun x -> tree_ens (g x) (cg x)) sl0 res sl1
  | TCif #a #guard  pre post thn els ->
             ite_ens #a guard (tree_ens _ thn) (tree_ens _ els) sl0 res sl1


(*** [repr] *)

/// The [repr] type contains a representation of the program as a tree and a corresponding steel function.

noeq inline_for_extraction noextract
type repr (ek : SH.effect_kind) (a : Type) = {
  repr_tree  : prog_tree a;
  repr_steel : (pre : pre_t) -> (post : post_t a) -> (c : tree_cond repr_tree pre post) ->
               repr_steel_t ek a pre post (tree_req repr_tree c) (tree_ens repr_tree c)
}
