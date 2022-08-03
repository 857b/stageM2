module Experiment.Steel.Repr.SF_to_Fun

module U   = Learn.Util
module Fl  = Learn.FList
module Dl  = Learn.DList
module Fun = Experiment.Repr.Fun

open Experiment.Steel.Repr.SF


(*** [sl_tys] *)

noeq
type sl_tys_r (ty : sl_tys_t u#a u#b) : Type u#(max a (b + 1)) = {
  vl : ty.val_t;
  sl : Dl.dlist (ty.sel_t vl)
}

/// By using [Fl.flist_of_d'] instead of [Fl.flist_of_d], we force the normalization of [x.sl], which improves
/// the normalization time of [elim_returns].
let sl_v_of_r (#ty : sl_tys_t u#a u#b) (x : sl_tys_r ty) : sl_tys_v ty = {
  val_v = x.vl;
  sel_v = Fl.flist_of_d' x.sl;
}

let sl_r_of_v (#ty : sl_tys_t u#a u#b) (x : sl_tys_v ty) : sl_tys_r ty = {
  vl = x.val_v;
  sl = Fl.dlist_of_f x.sel_v;
}

let sl_vrv (ty : sl_tys_t u#a u#b) (x : sl_tys_v ty)
  : Lemma (sl_v_of_r (sl_r_of_v x) == x) [SMTPat (sl_v_of_r (sl_r_of_v x))]
  = ()

let sl_rvr (ty : sl_tys_t u#a u#b) (x : sl_tys_r ty)
  : Lemma (sl_r_of_v (sl_v_of_r x) == x) [SMTPat (sl_r_of_v (sl_v_of_r x))]
  = ()


let sl_all (ty : sl_tys_t) (f : sl_tys_v ty -> Type0)
  : Type0
  =
   (forall (val_v : ty.val_t) . Fl.forall_flist (ty.sel_t val_v) (fun sel_v -> f ({val_v; sel_v})))


let sl_all_iff (ty : sl_tys_t) (f : sl_tys_v ty -> Type0)
  : Lemma (sl_all ty f  <==> (forall (x : sl_tys_v ty) . f x))
          [SMTPat (sl_all ty f)]
  =
    assert (forall (x : sl_tys_v ty) . x == {val_v = x.val_v; sel_v = x.sel_v})

let sl_ex (ty : sl_tys_t) (f : sl_tys_v ty -> Type0)
  : Type0
  =
   (exists (val_v : ty.val_t) . Fl.exists_flist (ty.sel_t val_v) (fun sel_v -> f ({val_v; sel_v})))

let sl_ex_iff (ty : sl_tys_t) (f : sl_tys_v ty -> Type0)
  : Lemma (sl_ex ty f  <==> (exists (x : sl_tys_v ty) . f x))
          [SMTPat (sl_ex ty f)]
  =
    assert (forall (x : sl_tys_v ty) . x == {val_v = x.val_v; sel_v = x.sel_v})


let sl_arw (src : sl_tys_t u#a u#b) (dst : Type u#d) : Type =
  (x : src.val_t) -> Fl.arw_list (src.sel_t x) dst

let sl_lam (src : sl_tys_t u#a u#b) (dst : Type u#d) (f : (x : src.val_t) -> (xs : Fl.flist (src.sel_t x)) -> dst)
  : sl_arw src dst
  = fun (x : src.val_t) -> Fl.lam_flist (src.sel_t x) dst (f x)

let sl_app (#src : sl_tys_t u#a u#b) (#dst : Type u#d) (f : sl_arw src dst) (x : sl_tys_v src) : dst
  = Fl.app_flist (f x.val_v) x.sel_v

let sl_app_lam (src : sl_tys_t u#a u#b) (dst : Type u#d)
               (f : (x : src.val_t) -> (xs : Fl.flist (src.sel_t x)) -> dst) (x : sl_tys_v src)
  : Lemma (ensures sl_app (sl_lam src dst f) x == f x.val_v x.sel_v)
          [SMTPat (sl_app (sl_lam src dst f) x)]
  = ()

unfold
let sl_uncurrify (#val_t : Type) (#sel_t : post_t val_t) (#dst : Type)
                 (f : (v : val_t) -> (sls : Fl.flist (sel_t v)) -> dst)
                 (x : sl_tys_v ({val_t; sel_t})) : dst
  = f x.val_v x.sel_v

unfold
let sl_tys' : Fun.tys' u#(max a b + 1) u#(max a (b + 1)) u#(max a (b + 1)) = {
  t = sl_tys_t u#a u#b;
  v = sl_tys_v u#a u#b;
  r = sl_tys_r u#a u#b;
  v_of_r = sl_v_of_r;
  r_of_v = sl_r_of_v;
  unit = {val_t = U.unit'; sel_t = (fun _ -> [])};
  emp  = {val_v = U.Unit'; sel_v = Fl.nil};
  all  = sl_all;
  ex   = sl_ex;
}

val sl_tys_hyp : unit -> Lemma (Fun.tys_hyp (sl_tys' u#a u#b))

let sl_tys : Fun.tys u#(max a b + 1) u#(max a (b + 1)) u#(max a (b + 1)) =
  (**) sl_tys_hyp ();
  sl_tys'


let delayed_sl_uncurrify
      (#val_t : Type) (#sel_t : post_t val_t) (#dst : Type)
      (f : (v : val_t) -> (sls : Fl.flist (sel_t v)) -> dst)
      (x : sl_tys_v ({val_t; sel_t})) : dst
  = f x.val_v x.sel_v 

unfold
let sl_tys_lam' : Fun.tys_lam' sl_tys = {
  lam_prop = (fun #src f -> delayed_sl_uncurrify #src.val_t #src.sel_t (fun val_v sel_v -> f ({val_v; sel_v})));
  lam_tree = (fun #src f -> delayed_sl_uncurrify #src.val_t #src.sel_t (fun val_v sel_v -> f ({val_v; sel_v})));
}

val sl_tys_lam_id : unit -> Lemma (Fun.tys_lam_id sl_tys_lam')

let sl_tys_lam : Fun.tys_lam sl_tys =
  (**) sl_tys_lam_id ();
  sl_tys_lam'


(*** Translation of the representation *)

[@@ strict_on_arguments [2]] (* strict on t *)
let rec repr_Fun_of_SF
          (#val_t : Type u#a) (#sel_t : post_t u#a u#b val_t) (t : prog_tree u#a u#b u#p val_t sel_t)
  : Tot (Fun.prog_tree u#(max a b + 1) u#(max a (b + 1)) u#(max a (b + 1)) u#p
                       #(sl_tys u#a u#b) ({val_t; sel_t}))
        (decreases t)
  = match t with
  | Tspec a post req ens ->
          Fun.Tspec ({val_t = a; sel_t = post}) req (sl_uncurrify ens)
  | Tret a x post sl ->
          Fun.Tret #sl_tys ({val_t = a; sel_t = post}) ({vl = x; sl})
  | Tbind a b itm post f g ->
          Fun.Tbind _ _ (repr_Fun_of_SF f) (sl_uncurrify (fun x sls -> repr_Fun_of_SF (g x sls)))
  | TbindP a b post wp g ->
          Fun.TbindP a ({val_t = b; sel_t = post}) wp (fun (x : a) -> repr_Fun_of_SF (g x))
  | Tif a guard post thn els ->
          Fun.Tif ({val_t = a; sel_t = post}) guard (repr_Fun_of_SF thn) (repr_Fun_of_SF els)
  | Twp a post wp ->
          Fun.Twp ({val_t = a; sel_t = post}) wp

[@@ strict_on_arguments [1]] (* strict on s *)
let rec shape_Fun_of_SF (#post_n : nat) (s : shape_tree post_n)
  : Tot (Fun.shape_tree) (decreases s)
  = match s with
  | Sspec _           -> Fun.Sspec
  | Sret  smp_ret _   -> Fun.Sret smp_ret
  | Sbind _ _ s_f s_g -> Fun.Sbind  (shape_Fun_of_SF s_f) (shape_Fun_of_SF s_g)
  | SbindP  _ s_g     -> Fun.SbindP (shape_Fun_of_SF s_g)
  | Sif   _ thn els   -> Fun.Sif    (shape_Fun_of_SF thn) (shape_Fun_of_SF els)
  | Swp   _           -> Fun.Swp
  


(*** Soundness *)

val repr_Fun_of_SF_req (#val_t : Type) (#sel_t : post_t val_t) (t : prog_tree u#a u#b u#p val_t sel_t)
  : Lemma (tree_req t <==> Fun.tree_req (repr_Fun_of_SF t))

val repr_Fun_of_SF_ens (#val_t : Type) (#sel_t : post_t val_t) (t : prog_tree u#a u#b u#p val_t sel_t)
                       (val_v : val_t) (sel_v : Fl.flist (sel_t val_v))
  : Lemma (tree_ens t val_v sel_v <==> Fun.tree_ens (repr_Fun_of_SF t) ({val_v; sel_v}))

val repr_Fun_of_SF_shape
      (#val_t : Type) (#sel_t : post_t val_t) (t : prog_tree u#a u#b u#p val_t sel_t)
      (s : prog_shape t)
  : Lemma (Fun.prog_has_shape (repr_Fun_of_SF t) (shape_Fun_of_SF s.shp))
