module Experiment.Steel.VEquiv

module U    = Learn.Util
module L    = FStar.List.Pure
module Ll   = Learn.List
module Fl   = Learn.FList
module Dl   = Learn.DList
module Mem  = Steel.Memory
module Opt  = Learn.Option
module Msk  = Learn.List.Mask
module Perm = Learn.Permutation
module Fext = FStar.FunctionalExtensionality

open Steel.Effect.Atomic
open Experiment.Steel.VPropList


irreducible let __vequiv__ : unit = ()

type veq_eq_t (pre_n post_n : nat) = Fext.(Fin.fin post_n ^-> option (Fin.fin pre_n))

unfold
let veq_eq_sl (#pre #post : vprop_list) (e : veq_eq_t (L.length pre) (L.length post))
  : veq_eq_t (L.length (vprop_list_sels_t pre)) (L.length (vprop_list_sels_t post))
  = U.cast _ e

[@@__vequiv__]
noextract
let mk_veq_eq (pre_n post_n : nat) (f : Fin.fin post_n -> option (Fin.fin pre_n))
  : veq_eq_t pre_n post_n
  = Fext.on (Fin.fin post_n) f

let veq_eq_t_list (pre_n post_n : nat) = Ll.vec post_n (option (Fin.fin pre_n))

[@@__vequiv__]
let veq_to_list (#pre_n #post_n : nat) (f : veq_eq_t pre_n post_n) : veq_eq_t_list pre_n post_n =
  Ll.initi 0 post_n f

[@@__vequiv__]
noextract
let veq_of_list (#pre_n #post_n : nat) (l : veq_eq_t_list pre_n post_n) : veq_eq_t pre_n post_n =
  Fext.on (Fin.fin post_n) (L.index l)

let veq_of_to_list #pre_n #post_n (f : veq_eq_t pre_n post_n)
  : Lemma (veq_of_list (veq_to_list f) == f)
          [SMTPat (veq_of_list (veq_to_list f))]
  = Fext.extensionality _ _ (veq_of_list (veq_to_list f)) f

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
          [SMTPat (veq_sel_eq_eff f_eq sl0 sl1)]


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
let veq_ens_eff (#pre #post : vprop_list) (veq : vequiv pre post) (sl0 : sl_f pre) (sl1 : sl_f post) : prop
  = veq.veq_ens sl0 sl1 /\ veq_sel_eq_eff (veq_eq_sl (veq_of_list veq.veq_eq)) sl0 sl1

[@@__vequiv__]
let veq_f (#pre #post : vprop_list) (veq : vequiv pre post) : veq_eq_t (L.length pre) (L.length post)
  = veq_of_list veq.veq_eq


(*** Building [vequiv] *)

[@@__vequiv__]
let vequiv_refl_eq (v : vprop_list)
  : veq_eq_t_list (L.length v) (L.length v)
  = Ll.initi 0 (L.length v) (fun i -> Some (i <: Fin.fin (L.length v)))

val vequiv_refl_sel_eq
      (#v: vprop_list) (sl0 : sl_f v) (sl1 : sl_f v)
  : squash (veq_sel_eq (veq_eq_sl (veq_of_list (vequiv_refl_eq v))) sl0 sl1 <==> sl1 == sl0)

[@@__vequiv__]
let vequiv_refl (v : vprop_list) : vequiv v v = {
  veq_req = (fun _ -> True);
  veq_ens = (fun _ _ -> True);
  veq_eq  = vequiv_refl_eq v;
  veq_typ = ();
  veq_g   = (fun opened -> noop ())
}

[@@__vequiv__]
let vequiv_with_req (#v0 #v1 : vprop_list) (req : Type0) (e : squash req -> vequiv v0 v1) : vequiv v0 v1 = {
  veq_req = (fun sl0     -> req /\ (e ()).veq_req sl0);
  veq_ens = (fun sl0 sl1 -> req /\ veq_ens_eff (e ()) sl0 sl1);
  // [veq_typ] cannot requires req so we do not propagate the equalities
  veq_eq  = L.map (fun _ -> None) v1;
  veq_typ = ();
  veq_g   = (fun opened -> (e ()).veq_g opened)
}

(***** [vequiv_trans] *)

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


(***** [vequiv_cons] *)

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

val vequiv_cons_g (hd : vprop') (#pre #post : vprop_list) (e : vequiv pre post) (opened : Mem.inames)
  : SteelGhost unit opened (vprop_of_list (hd :: pre)) (fun () -> vprop_of_list (hd :: post))
      (requires fun h0       -> e.veq_req (Fl.tail #hd.t #(vprop_list_sels_t  pre) (sel (hd :: pre) h0)))
      (ensures  fun h0 () h1 -> let sl0 = sel (hd :: pre) h0 in
                             let sl1 = sel (hd :: post) h1 in
                             e.veq_ens (Fl.tail #hd.t #(vprop_list_sels_t  pre) sl0)
                                       (Fl.tail #hd.t #(vprop_list_sels_t post) sl1) /\
                             veq_sel_eq (U.cast _ (veq_of_list (vequiv_cons_eq e.veq_eq))) sl0 sl1)

[@@__vequiv__]
let vequiv_cons (hd : vprop') (#pre #post : vprop_list) (e : vequiv pre post)
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


(***** [vequiv_app] *)

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
               Ll.map_append Mkvprop'?.t pre0 pre1;
               Ll.map_append Mkvprop'?.t post0 post1;
               ());
    veq_g   = vequiv_app_g e0 e1
   }


(***** [vequiv_of_perm] *)

[@@__vequiv__]
let vequiv_of_perm_eq (#pre #post : vprop_list) (f : vequiv_perm pre post)
  : veq_eq_t (L.length pre) (L.length post)
  = mk_veq_eq (L.length pre) (L.length post) (fun i -> Some (f i))

val vequiv_of_perm_sel_eq
      (#pre #post : vprop_list) (f : vequiv_perm pre post)
      (sl0 : sl_f pre) (sl1 : sl_f post)
  : squash (veq_sel_eq (veq_eq_sl (vequiv_of_perm_eq f)) sl0 sl1 <==> sl1 == extract_vars f sl0)

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


(***** [vequiv_inj] *)

(**) private val __begin_vequiv_inj : unit

let injective_on_dom (#a #b : Type) (f : a -> option b) : prop =
  forall (x x' : a) . Some? (f x) /\ f x == f x' ==> x == x'

let injective_on_domI (#a #b : Type) (f : a -> option b)
                      (prf : (x : a) -> (x' : a) -> Lemma (requires Some? (f x) /\ f x == f x') (ensures x == x'))
  : Lemma (injective_on_dom f)
  = FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 prf)

let map_to_eq (#a : Type) (src trg : list a) (f : Fin.fin (L.length src) -> option (Fin.fin (L.length trg)))
  : prop
  = forall (i : Fin.fin (L.length src)) . Some? (f i) ==> L.index trg (Some?.v (f i)) == L.index src i

/// The type of partial injection between equal elements of two lists.
/// In practice [a] is [vprop']
type partial_injection (#a : Type) (src trg : list a) =
  f : Ll.vec (L.length src) (option (Fin.fin (L.length trg))) {
    map_to_eq src trg (L.index f) /\
    injective_on_dom #(Fin.fin (L.length src)) (L.index f)
  }

// Used instead of [L.mem (Some x) l] to avoid problems of reduction of [Some #t x = Some #t' y]
[@@__vequiv__]
let rec mem_Some (#a : eqtype) (x : a) (l : list (option a))
  : Tot bool (decreases l) =
  match l with
  | [] -> false
  | None :: l -> mem_Some x l
  | Some y :: l -> y = x || mem_Some x l

val mem_Some_eq (#a : eqtype) (x : a) (l : list (option a))
  : Lemma (mem_Some x l = L.mem (Some x) l) [SMTPat (mem_Some x l)]


/// Masks to select the elements that have *not* been matched

[@@ __vequiv__]
let ij_src_mask (#src_n : nat) (#b : Type) (ij : Ll.vec src_n (option b)) : Ll.vec src_n bool
  = L.map None? ij

[@@ __vequiv__]
let ij_trg_mask (#src_n #trg_n : nat) (ij : Ll.vec src_n (option (Fin.fin trg_n))) : Ll.vec trg_n bool
  = Ll.initi 0 trg_n (fun j -> not (mem_Some j ij))

/// Number of matched elements i.e. number of [Some]
let ij_matched_n (#a : Type) (#src #trg : list a) (ij : partial_injection src trg) : nat
  = Msk.mask_len (Msk.mask_not (ij_src_mask ij))

let ij_matched_perm_f (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
                    (i : Fin.fin (Msk.mask_len (Msk.mask_not (ij_src_mask ij))))
  : Fin.fin (Msk.mask_len (Msk.mask_not (ij_trg_mask ij)))
  =
    let i0 = Msk.mask_pull (Msk.mask_not (ij_src_mask ij)) i in
    let j0 = Some?.v (L.index ij i0) in
    (**) L.lemma_index_memP ij i0;
    Msk.mask_push (Msk.mask_not (ij_trg_mask ij)) j0

val ij_matched_perm_f_injective
      (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (Perm.injective (ij_matched_perm_f ij))

val ij_matched_perm_f_surjective
      (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (Perm.surjective (ij_matched_perm_f ij))

val ij_matched_len (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (Msk.mask_len (Msk.mask_not (ij_trg_mask ij)) = Msk.mask_len (Msk.mask_not (ij_src_mask ij)))

let ij_matched_perm (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Perm.perm_f (ij_matched_n ij)
  = 
    (**) ij_matched_perm_f_injective ij;
    (**) ij_matched_len ij;
    Perm.mk_perm_f _ (ij_matched_perm_f ij)

val ij_matched_perm_eq (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Lemma (ij_matched_len ij;
           Msk.filter_mask (Msk.mask_not (ij_src_mask ij)) src ==
           Perm.apply_perm_r (ij_matched_perm ij) (Msk.filter_mask (Msk.mask_not (ij_trg_mask ij)) trg))

let ij_matched_equiv (#a : Type) (#src #trg : list a) (ij : partial_injection src trg)
  : Perm.pequiv (Msk.filter_mask (Msk.mask_not (ij_trg_mask ij)) trg)
                (Msk.filter_mask (Msk.mask_not (ij_src_mask ij)) src)
  =
    (**) let l_trg = Msk.filter_mask (Msk.mask_not (ij_trg_mask ij)) trg in
    (**) ij_matched_len ij;
    (**) ij_matched_perm_eq ij;
    U.cast (Perm.perm_f (L.length l_trg)) (ij_matched_perm ij)


[@@ __vequiv__]
let vequiv_inj_eq
      (#src #trg : vprop_list)
      (ij : partial_injection src trg)
      (e' : vequiv (Msk.filter_mask (ij_trg_mask ij) trg) (Msk.filter_mask (ij_src_mask ij) src))
  : veq_eq_t_list (L.length trg) (L.length src)
  =
    let mask_src = ij_src_mask ij in
    let mask_trg = ij_trg_mask ij in
    Msk.merge_fun_on_mask mask_src #(option (Fin.fin (L.length trg)))
        (fun _ j -> Opt.map (Msk.mask_pull mask_trg) (veq_f e' j))
        (fun i _ -> L.index ij i)

val vequiv_inj_typ
      (#src #trg : vprop_list)
      (ij : partial_injection src trg)
      (e' : vequiv (Msk.filter_mask (ij_trg_mask ij) trg) (Msk.filter_mask (ij_src_mask ij) src))
  : squash (veq_typ_eq (vprop_list_sels_t trg) (vprop_list_sels_t src)
                         (U.cast _ (veq_of_list (vequiv_inj_eq ij e'))))

val vequiv_inj_g
      (#src #trg : vprop_list)
      (ij : partial_injection src trg)
      (e' : vequiv (Msk.filter_mask (ij_trg_mask ij) trg) (Msk.filter_mask (ij_src_mask ij) src))
      (opened : Steel.Memory.inames)
  : Steel.Effect.Atomic.SteelGhost unit opened (vprop_of_list trg) (fun () -> vprop_of_list src)
      (requires fun h0 ->
                 e'.veq_req (Msk.filter_mask_fl (ij_trg_mask ij) _ (sel trg h0)))
      (ensures  fun h0 () h1 ->
                 e'.veq_ens (Msk.filter_mask_fl (ij_trg_mask ij) _ (sel trg h0))
                            (Msk.filter_mask_fl (ij_src_mask ij) _ (sel src h1)) /\
                 veq_sel_eq (veq_eq_sl (veq_of_list (vequiv_inj_eq ij e')))
                                (sel trg h0) (sel src h1))

//TODO? [filter_mask_dl] instead of [filter_mask_fl]
[@@ __vequiv__]
let vequiv_inj
      (src : vprop_list) (trg : vprop_list)
      (ij : partial_injection src trg)
      (e' : vequiv (Msk.filter_mask (ij_trg_mask ij) trg) (Msk.filter_mask (ij_src_mask ij) src))
  : vequiv trg src
  =
    let mask_src = ij_src_mask ij in
    let mask_trg = ij_trg_mask ij in
  {
    veq_req = (fun (sl0 : sl_f trg) ->
                 e'.veq_req (Msk.filter_mask_fl mask_trg _ sl0));
    veq_ens = (fun (sl0 : sl_f trg) (sl1 : sl_f src) ->
                 e'.veq_ens (Msk.filter_mask_fl mask_trg _ sl0) (Msk.filter_mask_fl mask_src _ sl1));
    veq_eq  = vequiv_inj_eq  ij e';
    veq_typ = (let _ = vequiv_inj_typ ij e' in ());
    veq_g   = vequiv_inj_g   ij e';
  }

[@@__vequiv__]
let extend_partial_injection #a (#src #trg : list a) (ij : partial_injection src trg) (src_add : list a)
  : partial_injection L.(src@src_add) trg
  =
    let f_add = L.map (fun _ -> None) src_add in
    let f = L.(ij @ f_add) in
    let src' = L.(src@src_add) in
    introduce forall (i : Fin.fin (L.length L.(src@src_add)) {Some? (L.index f i)}).
                  i < L.length src /\ L.index f i == L.index ij i
      with Ll.append_index ij f_add i;
    introduce (forall (i : Fin.fin (L.length src')) . Some? (L.index f i) ==>
                L.index trg (Some?.v (L.index f i)) == L.index src' i) /\
              injective_on_dom #(Fin.fin (L.length src')) (L.index f)
      with introduce forall i . _
           with introduce Some? (L.index f i) ==> L.index trg (Some?.v (L.index f i)) == L.index src' i
           with _ . Ll.append_index src src_add i
      and ();
    f

val extend_partial_injection_src (#a : Type) (#src #trg : list a)
                                 (ij : partial_injection src trg) (src_add : list a)
  : Lemma (Msk.filter_mask (ij_src_mask (extend_partial_injection ij src_add)) L.(src@src_add)
        == L.append (Msk.filter_mask (ij_src_mask ij) src) src_add)

val extend_partial_injection_trg (#a : Type) (#src #trg : list a)
                                 (ij : partial_injection src trg) (src_add : list a)
  : Lemma (Msk.filter_mask (ij_trg_mask (extend_partial_injection ij src_add)) trg
        == Msk.filter_mask (ij_trg_mask ij) trg)
