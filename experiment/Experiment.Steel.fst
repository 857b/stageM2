module Experiment.Steel

module SF     = Experiment.Steel.Repr.SF
module SF2Fun = Experiment.Steel.Repr.SF_to_Fun


#set-options "--ide_id_info_off --ifuel 0"

(**) #push-options "--ifuel 0"
(**) private let __begin_prog_to_Fun = ()
(**) #pop-options
(**) private let __end_prog_to_Fun = ()


#push-options "--ifuel 0 --fuel 0"
let prog_LV_to_Fun_equiv_M
      (#ek : SH.effect_kind) (#a : Type) (t : M.repr ek a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (lc : LV.top_lin_cond t.repr_tree pre post {LV.lcsub_at_leaves lc})
      (sl0 : Vpl.sl_f pre)
  : Lemma (prog_M_equiv_Fun t.repr_tree (LV2M.repr_M_of_LV_top lc) sl0 (prog_LV_to_Fun t lc sl0))
  =
    let tr    = t.repr_tree                  in
    let mc    = LV2M.repr_M_of_LV_top lc     in
    let sl0_l = Fl.dlist_of_f sl0            in
    let t_SF  = LV2SF.repr_SF_of_LV lc sl0_l in
    let t_Fun = prog_LV_to_Fun t lc sl0      in

    LV2M.repr_M_of_LV_top_sound lc;
    LV2SF.repr_SF_of_LV_sound lc sl0_l;
    SF2Fun.repr_Fun_of_SF_req t_SF;

    let lem_req () : Lemma (M.tree_req t.repr_tree mc sl0 <==> Fun.tree_req t_Fun) = () in
    let lem_ens (x : a) (sl1 : Vpl.sl_f (post x))
      : Lemma (M.tree_ens tr mc sl0 x sl1 <==> Fun.tree_ens t_Fun ({val_v = x; sel_v = sl1}))
      = SF2Fun.repr_Fun_of_SF_ens t_SF x sl1
    in
    assert (prog_M_equiv_Fun t.repr_tree (LV2M.repr_M_of_LV_top lc) sl0 (prog_LV_to_Fun t lc sl0))
      by (norm [delta_only [`%prog_M_equiv_Fun]];
          split ();
            apply_lemma (``@lem_req);
            let _ = mintros () in apply_lemma (``@lem_ens))
#pop-options
