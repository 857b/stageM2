module Experiment.Steel.Repr.ST_to_SF.Base

module T = FStar.Tactics

open FStar.Classical.Sugar
open FStar.Calc


#push-options "--fuel 2 --z3rlimit 30"
let rec repr_SF_of_ST_req
      (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
      (t : ST.prog_tree a pre post)
      (sl0 : Fl.flist pre)
  : Lemma (ensures ST.tree_req t sl0 <==> tree_req (repr_SF_of_ST t sl0)) (decreases t)
  = ST.match_prog_tree t
    (fun a pre post t -> (sl0 : Fl.flist pre) ->
       squash (ST.tree_req t sl0 <==> tree_req (repr_SF_of_ST t sl0)))
    (fun (*ST.Tequiv*) pre post0 p -> fun sl0 -> ())
    begin fun (*ST.Tframe*) a pre post frame f -> fun sl0 ->
      let (sl0', sl_frame) = Fl.splitAt_ty pre frame sl0 in
      repr_SF_of_ST_req f sl0'
    end
    (fun (*ST.Tspec*) a pre post req ens -> fun sl0 -> ())
    (fun (*ST.Tret*) a x post -> fun sl0 -> ())
    begin fun (*ST.Tbind*) a b pre itm post f g -> fun sl0 ->
      calc (<==>) {
        ST.tree_req (ST.Tbind a b pre itm post f g) sl0;
      == { _ by T.(trefl ()) }
        ST.tree_req f sl0 /\
        (forall (x : a) (sl1 : Fl.flist (itm x)) .
          ST.tree_ens f sl0 x sl1 ==> ST.tree_req (g x) sl1);
      <==> { repr_SF_of_ST_req f sl0;
           introduce forall (x : a) (sl1 : Fl.flist (itm x)) .
               (ST.tree_ens f sl0 x sl1 <==> tree_ens (repr_SF_of_ST f sl0) x sl1) /\
               (ST.tree_req (g x) sl1 <==> tree_req (repr_SF_of_ST (g x) sl1))
             with (repr_SF_of_ST_ens f sl0 x sl1; repr_SF_of_ST_req (g x) sl1) }
        tree_req (repr_SF_of_ST f sl0) /\
        (forall (x : a) (sl1 : Fl.flist (itm x)) .
          tree_ens (repr_SF_of_ST f sl0) x sl1 ==> tree_req (repr_SF_of_ST (g x) sl1));
      == { _ by T.(trefl ()) }
        tree_req (repr_SF_of_ST (ST.Tbind a b pre itm post f g) sl0);
      }
    end
    begin fun (*ST.TbindP*) a b pre post wp g -> fun sl0 ->
      introduce forall (x : a) .
          ST.tree_req (g x) sl0 <==> tree_req (repr_SF_of_ST (g x) sl0)
        with repr_SF_of_ST_req (g x) sl0;
      FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp
    end
    begin fun (*ST.Tif*) a guard pre post thn els -> fun sl0 ->
      if guard
      then repr_SF_of_ST_req thn sl0
      else repr_SF_of_ST_req els sl0
    end sl0

and repr_SF_of_ST_ens
      (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
      (t : ST.prog_tree a pre post)
      (sl0 : Fl.flist pre) (res : a) (sl1 : Fl.flist (post res))
  : Lemma (ensures ST.tree_ens t sl0 res sl1 <==> tree_ens (repr_SF_of_ST t sl0) res sl1) (decreases t)
  = ST.match_prog_tree t
    (fun a pre post t -> (sl0 : Fl.flist pre) -> (res : a) -> (sl1 : Fl.flist (post res)) ->
       squash (ST.tree_ens t sl0 res sl1 <==> tree_ens (repr_SF_of_ST t sl0) res sl1))
    (fun (*ST.Tequiv*) pre post0 e -> fun sl0 res sl1 -> Veq.veq_sel_eq_eff_sound e.seq_eq sl0 sl1)
    begin fun (*ST.Tframe*) a pre post frame f -> fun sl0 x sl1 ->
      let sl0', sl_frame = Fl.splitAt_ty pre frame sl0 in
      calc (<==>) {
        ST.tree_ens (ST.Tframe a pre post frame f) sl0 x sl1;
      == { _ by T.(norm [delta_only [`%ST.tree_ens]; iota; zeta]; trefl ()) }
       (let sl0', sl_frame = Fl.splitAt_ty pre frame sl0 in
        exists (sl1' : post_v post x) .
          ST.tree_ens f sl0' x sl1' /\ sl1 == Fl.append sl1' sl_frame);
      <==> { FStar.Classical.forall_intro (repr_SF_of_ST_ens f sl0' x) }
        exists (sl1' : post_v post x) .
          tree_ens (repr_SF_of_ST f sl0') x sl1' /\ sl1 == Fl.append sl1' sl_frame;
      <==> { }
        tree_ens (repr_SF_of_ST (ST.Tframe a pre post frame f) sl0) x sl1;
      }
    end
    (fun (*ST.Tspec*) a pre post req ens -> fun sl0 res sl1 -> ())
    (fun (*ST.Tret*) a x post -> fun sl0 res sl1 -> ())
    begin fun (*ST.Tbind*) a b pre itm post f g -> fun sl0 y sl2 ->
      calc (<==>) {
        ST.tree_ens (ST.Tbind a b pre itm post f g) sl0 y sl2;
      == { _ by T.(trefl ()) }
        exists (x : a) (sl1 : post_v itm x) .
          ST.tree_ens f sl0 x sl1 /\ ST.tree_ens (g x) sl1 y sl2;
      <==> { introduce forall (x : a) (sl1 : post_v itm x) .
               (ST.tree_ens f sl0 x sl1 /\ ST.tree_ens (g x) sl1 y sl2) <==>
               (tree_ens (repr_SF_of_ST f sl0) x sl1 /\ tree_ens (repr_SF_of_ST (g x) sl1) y sl2)
             with (repr_SF_of_ST_ens f sl0 x sl1; repr_SF_of_ST_ens (g x) sl1 y sl2) }
        exists (x : a) (sl1 : post_v itm x) .
          tree_ens (repr_SF_of_ST f sl0) x sl1 /\ tree_ens (repr_SF_of_ST (g x) sl1) y sl2;
      == { _ by T.(trefl ()) }
        tree_ens (repr_SF_of_ST (ST.Tbind a b pre itm post f g) sl0) y sl2;
      }
    end
    begin fun (*ST.TbindP*) a b pre post wp g -> fun sl0 y sl1 ->
      calc (<==>) {
        ST.tree_ens (ST.TbindP a b pre post wp g) sl0 y sl1;
      == { _ by T.(trefl ()) }
        exists (x : a) . as_ensures wp x /\ ST.tree_ens (g x) sl0 y sl1;
      <==> { introduce forall (x : a) .
               ST.tree_ens (g x) sl0 y sl1 <==> tree_ens (repr_SF_of_ST (g x) sl0) y sl1
             with repr_SF_of_ST_ens (g x) sl0 y sl1 }
        exists (x : a) . as_ensures wp x /\ tree_ens (repr_SF_of_ST (g x) sl0) y sl1;
      == { _ by T.(trefl ()) }
        tree_ens (repr_SF_of_ST (ST.TbindP a b pre post wp g) sl0) y sl1;
      }
    end
    begin fun (*ST.Tif*) a guard pre post thn els -> fun sl0 x sl1 ->
      if guard
      then repr_SF_of_ST_ens thn sl0 x sl1
      else repr_SF_of_ST_ens els sl0 x sl1
    end sl0 res sl1
#pop-options

#push-options "--fuel 2 --z3rlimit 20"
let rec repr_SF_of_ST_shape
      (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
      (t : ST.prog_tree a pre post)
      (#post_n : nat) (s : ST.shape_tree (L.length pre) post_n)
      (sl0 : Fl.flist pre)
  : Lemma (requires ST.prog_has_shape t s)
          (ensures  prog_has_shape (repr_SF_of_ST t sl0) (shape_SF_of_ST s))
          (decreases t)
  = ST.match_prog_tree t
    (fun a pre post t -> (#post_n : nat) -> (s : ST.shape_tree (L.length pre) post_n) ->
       squash (ST.prog_has_shape t s) ->
       (sl0 : Fl.flist pre) -> 
       squash (prog_has_shape (repr_SF_of_ST t sl0) (shape_SF_of_ST s)))
    (fun (*ST.Tequiv*) pre post0 p -> fun s _ sl0 -> ())
    begin fun (*ST.Tframe*) a pre post frame f -> fun s _ sl0 ->
      let ST.Sframe _ post_n _ s_f = s            in
      let sl0' = (Fl.splitAt_ty pre frame sl0)._1 in
      repr_SF_of_ST_shape f s_f sl0'
    end
    (fun (*ST.Tspec*) a pre post req ens -> fun s _ sl0 -> ())
    (fun (*ST.Tret*) a x post -> fun s _ sl0 -> ())
    begin fun (*ST.Tbind*) a b pre itm post f g -> fun s _ sl0 ->
      let ST.Sbind _ itm_n post_n s_f s_g = s in
      repr_SF_of_ST_shape f s_f sl0;
      introduce forall (x : a) (sl1 : Fl.flist (itm x)) .
           prog_has_shape (repr_SF_of_ST (g x) sl1) (shape_SF_of_ST s_g)
        with repr_SF_of_ST_shape (g x) s_g sl1
    end
    begin fun (*ST.TbindP*) a b pre post wp g -> fun s _ sl0 ->
      let ST.SbindP _ post_n s_g = s in
      let lem_g (x : a)
        : Lemma (prog_has_shape (repr_SF_of_ST (g x) sl0) (shape_SF_of_ST s_g))
                [SMTPat (g x)]
        = repr_SF_of_ST_shape (g x) s_g sl0
      in ()
    end
    begin fun (*ST.Tif*) a guard pre post thn els -> fun s _ sl0 ->
      let ST.Sif _ _ s_thn s_els = s in
      repr_SF_of_ST_shape thn s_thn sl0;
      repr_SF_of_ST_shape els s_els sl0
    end s () sl0
#pop-options
