module Experiment.Steel.Repr.SF

module T = FStar.Tactics
open FStar.Calc
open Learn.Logic


(*** Steel.Repr.SF --> Repr.Fun *)

let __begin_repr_fun_of_steel = ()

module Fun = Experiment.Repr.Fun


let sl_tys_hyp () : Lemma (Fun.tys_hyp (sl_tys' u#a u#b)) =
  introduce forall (x : sl_tys'.v sl_tys'.unit) . x == sl_tys'.emp
    with Fl.nil_uniq x.sel_v;
  assert (Fun.tys_hyp sl_tys') by T.(norm [delta_only [`%Fun.tys_hyp]])

let sl_tys_lam_id ()
  : Lemma (Fun.tys_lam_id sl_tys_lam')
  =
    let s  = sl_tys      in
    let lm = sl_tys_lam' in
    introduce forall (src : sl_tys_t) (f : pure_post (sl_tys_v src)) .
            lm.lam_prop f == (fun (x : sl_tys_v src) -> f x)
    with begin
      let {val_t; sel_t} = src <: sl_tys_t in
      U.funext_eta_gtot (sl_tys_lam'.lam_prop #({val_t; sel_t}) f)
                   (fun (x : sl_tys_v ({val_t; sel_t})) -> f x)
        (_ by T.(trefl ())) (_ by T.(trefl())) (fun x -> ());
      U.prop_equal (fun (src' : sl_tys_t {src' == src}) ->
                      sl_tys_lam'.lam_prop f == (fun (x : sl_tys_v src') -> f x))
                   ({val_t; sel_t}) src
    end;
  introduce forall (src : sl_tys_t) (trg : Type) (f : sl_tys_v src -> trg).
              lm.lam_tree #src #trg f == (fun (x : sl_tys_v src) -> f x)
    with begin
      let {val_t; sel_t} = src <: sl_tys_t in
      U.funext_eta (sl_tys_lam'.lam_tree #({val_t; sel_t}) #trg f)
                   (fun (x : sl_tys_v ({val_t; sel_t})) -> f x)
        (_ by T.(trefl ())) (_ by T.(trefl())) (fun x -> ());
      U.prop_equal (fun (src' : sl_tys_t {src' == src}) ->
                      sl_tys_lam'.lam_tree #src' #trg f == (fun (x : sl_tys_v src') -> f x))
                   ({val_t; sel_t}) src
    end;
  assert (Fun.tys_lam_id #s lm)
    by T.(norm [delta_only [`%Fun.tys_lam_id; `%sl_tys; `%Fun.Mktys'?.t; `%Fun.Mktys'?.v]])

//FIXME this proof succeeds in interactive mode with --fuel 1 but not in batch mode
//      (both wihout hints)
#push-options "--z3rlimit 40 --ifuel 1 --fuel 2"
let rec repr_Fun_of_SF_req #val_t #sel_t (t : prog_tree val_t sel_t)
  : Lemma (ensures tree_req t <==> Fun.tree_req (repr_Fun_of_SF t))
          (decreases t)
  = match t with
  | Tspec a post req ens -> ()
  | Tret a x post sl -> ()
  | Tbind a b itm post f g ->
          repr_Fun_of_SF_req f;
          introduce forall (x : a) (sl1 : post_v itm x) .
                    (tree_ens f x sl1   <==> Fun.tree_ens (repr_Fun_of_SF f) ({val_v=x; sel_v=sl1})) /\
                    (tree_req (g x sl1) <==> Fun.tree_req (repr_Fun_of_SF (g x sl1)))
            with (repr_Fun_of_SF_ens f x sl1; repr_Fun_of_SF_req (g x sl1))
  | TbindP a b post wp g ->
          calc (<==>) {
            tree_req (TbindP a b post wp g);
          <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
            wp (fun x -> tree_req (g x));
          <==> {wp_morph_iff wp (fun x -> tree_req (g x)) (fun x -> Fun.tree_req (repr_Fun_of_SF (g x)))
                              (fun x -> repr_Fun_of_SF_req (g x))}
            wp (fun x -> Fun.tree_req (repr_Fun_of_SF (g x)));
          <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
            Fun.tree_req (repr_Fun_of_SF (TbindP a b post wp g));
          }
  | Tif a guard post thn els ->
          if guard
          then repr_Fun_of_SF_req thn
          else repr_Fun_of_SF_req els

and repr_Fun_of_SF_ens #val_t #sel_t (t : prog_tree val_t sel_t)
                          (val_v : val_t) (sel_v : Fl.flist (sel_t val_v))
  : Lemma (ensures tree_ens t val_v sel_v <==> Fun.tree_ens (repr_Fun_of_SF t) ({val_v; sel_v}))
          (decreases t)
  = match t with
  | Tspec a post req ens ->
          assert (tree_ens (Tspec a post req ens) val_v sel_v == ens val_v sel_v)
               by T.(trefl ());
          assert (Fun.tree_ens (repr_Fun_of_SF (Tspec a post req ens)) ({val_v; sel_v})
               == sl_uncurrify ens ({val_v; sel_v}))
               by T.(trefl ())
  | Tret a x post sl -> ()
  | Tbind a b itm post f g ->
          assert (tree_ens (Tbind a b itm post f g) val_v sel_v
               == (exists (x : a) (sl1 : post_v itm x) . tree_ens f x sl1 /\ tree_ens (g x sl1) val_v sel_v) )
               by T.(trefl ());
          assert (Fun.tree_ens (repr_Fun_of_SF (Tbind a b itm post f g)) ({val_v; sel_v})
               == sl_tys.ex ({val_t=a; sel_t=itm}) (fun (x_sl1 : sl_tys_v ({val_t=a; sel_t=itm})) ->
                     Fun.tree_ens (repr_Fun_of_SF f) x_sl1 /\
                     Fun.tree_ens
                      (sl_uncurrify (fun x sls -> repr_Fun_of_SF (g x sls)) x_sl1) ({val_v; sel_v})))
               by T.(norm [delta_only [`%repr_Fun_of_SF; `%Fun.tree_ens]; iota; zeta];
                     trefl ());
          introduce forall (x : a) (sl1 : post_v itm x) .
                    (tree_ens f x sl1   <==> Fun.tree_ens (repr_Fun_of_SF f) ({val_v=x; sel_v=sl1})) /\
                    (tree_ens (g x sl1) val_v sel_v <==> Fun.tree_ens (repr_Fun_of_SF (g x sl1)) ({val_v; sel_v}))
            with (repr_Fun_of_SF_ens f x sl1; repr_Fun_of_SF_ens (g x sl1) val_v sel_v)
  | TbindP a b post wp g ->
          assert (tree_ens (TbindP a b post wp g) val_v sel_v
              == (exists (x : a) . as_ensures wp x /\ tree_ens (g x) val_v sel_v))
            by T.(trefl ());
          assert (Fun.tree_ens (repr_Fun_of_SF (TbindP a b post wp g)) ({val_v; sel_v})
              <==> (exists (x : a) .
                   (exists (nl : Fl.flist []) . as_ensures (add_sl_to_wp wp) ({val_v = x; sel_v = nl})) /\
                   Fun.tree_ens (repr_Fun_of_SF (g x)) ({val_v; sel_v})))
            by T.(norm [delta_only [`%Fun.tree_ens; `%repr_Fun_of_SF; `%sl_uncurrify;
                                    `%sl_tys; `%sl_tys'; `%Fun.Mktys'?.ex; `%sl_ex;
                                    `%Mksl_tys_t?.val_t; `%Mksl_tys_t?.sel_t];
                        iota; zeta]; smt ());
          introduce forall (x : a) .
              ((exists (nl : Fl.flist []) . as_ensures (add_sl_to_wp wp) ({val_v = x; sel_v = nl})) <==>
                  as_ensures wp x) /\
              (tree_ens (g x) val_v sel_v <==> Fun.tree_ens (repr_Fun_of_SF (g x)) ({val_v; sel_v}))
            with introduce _ /\ _
            with FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp
             and repr_Fun_of_SF_ens (g x) val_v sel_v
  | Tif a guard post thn els ->
          if guard
          then repr_Fun_of_SF_ens thn val_v sel_v
          else repr_Fun_of_SF_ens els val_v sel_v

#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec repr_Fun_of_SF_shape
      (#val_t : Type) (#sel_t : post_t val_t) (t : prog_tree u#a u#b val_t sel_t)
      (s : prog_shape t)
  : Lemma (ensures Fun.prog_has_shape (repr_Fun_of_SF t) (shape_Fun_of_SF s.shp))
          (decreases t)
  = match t with
  | Tspec _ _ _ _ | Tret _ _ _ _ -> ()
  | Tbind a b itm post f g ->
          let Sbind _ _ s_f s_g = s.shp in
          repr_Fun_of_SF_shape f (mk_prog_shape f s_f);
          introduce forall (x : sl_tys_v ({val_t = a; sel_t = itm})) .
              Fun.prog_has_shape ((sl_uncurrify (fun x sls -> repr_Fun_of_SF (g x sls))) x)
                                 (shape_Fun_of_SF s_g)
            with repr_Fun_of_SF_shape (g x.val_v x.sel_v) (mk_prog_shape _ s_g)
  | TbindP a b post wp g ->
          let SbindP _ s_g = s.shp in
          introduce forall (x : a) .
              Fun.prog_has_shape (repr_Fun_of_SF (g x)) (shape_Fun_of_SF s_g)
            with repr_Fun_of_SF_shape (g x) (mk_prog_shape _ s_g)
  | Tif a guard post thn els ->
          let Sif _ s_thn s_els = s.shp in
          repr_Fun_of_SF_shape thn (mk_prog_shape thn s_thn);
          repr_Fun_of_SF_shape els (mk_prog_shape els s_els)
#pop-options
