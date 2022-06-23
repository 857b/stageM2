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
    let tr    = t.repr_tree                in
    let mc    = LV2M.repr_M_of_LV_top lc   in
    let t_SF  = LV2SF.repr_SF_of_LV lc sl0 in
    let t_Fun = prog_LV_to_Fun t lc sl0    in

    LV2M.repr_M_of_LV_top_sound lc;
    LV2SF.repr_SF_of_LV_sound lc sl0;
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


(***** Calling a [M.repr_steel_t] from a Steel program *)

inline_for_extraction
let steel_subcomp_eq
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a)
      (req_f : SE.req_t pre) (ens_f : SE.ens_t pre a post)
      (req_g : SE.req_t pre) (ens_g : SE.ens_t pre a post)
      (pf_req : unit -> squash (req_f == req_g))
      (pf_ens : unit -> squash (ens_f == ens_g))
      (f : SH.unit_steel a pre post req_f ens_f)
  : SH.unit_steel a pre post req_g ens_g
  = pf_req ();
    pf_ens ();
    U.cast #(SH.unit_steel a pre post req_f ens_f) (SH.unit_steel a pre post req_g ens_g) f


#push-options "--ifuel 1"
inline_for_extraction
let __call_repr_steel_0
      (#a : Type)
      (#pre : M.pre_t)     (#post : M.post_t a)
      (#req : M.req_t pre) (#ens  : M.ens_t pre a post)
      (r : M.repr_steel_t SH.KSteel a pre post req ens)
  : SH.unit_steel a (Vpl.vprop_of_list pre) (fun x -> Vpl.vprop_of_list (post x))
      (requires fun h0      -> req (norm_vpl (Vpl.sel_f' pre h0)))
      (ensures  fun h0 x h1 -> ens (norm_vpl (Vpl.sel_f' pre h0)) x (norm_vpl (Vpl.sel_f' (post x) h1)))
  = steel_subcomp_eq
      #a #(Vpl.vprop_of_list pre) #(fun x -> Vpl.vprop_of_list (post x))
      (fun h0 -> req (Vpl.sel pre h0))
      (fun h0 x h1 -> ens (Vpl.sel pre h0) x (Vpl.sel (post x) h1))
      (fun h0 -> req (norm_vpl (Vpl.sel_f' pre h0)))
      (fun h0 x h1 -> ens (norm_vpl (Vpl.sel_f' pre h0)) x (norm_vpl (Vpl.sel_f' (post x) h1)))
      (fun () -> _ by (pointwise (fun () -> try exact (`Vpl.sel_eq') with | _ -> trefl ());
                    norm [delta_only [`%norm_vpl]]; trefl ()))
      (fun () -> _ by (pointwise (fun () -> try exact (`Vpl.sel_eq') with | _ -> trefl ());
                    norm [delta_only [`%norm_vpl]]; trefl ()))
      (SH.steel_u r)
#pop-options

inline_for_extraction
let call_repr_steel #a #pre #post #req #ens r = __call_repr_steel_0 r ()
