module Experiment.Steel

module SF = Experiment.Steel.Repr.SF

#set-options "--ide_id_info_off --ifuel 1"

(**) #push-options "--ifuel 0"
(**) private let __begin_prog_M_to_Fun = ()
(**) #pop-options
(**) private let __end_prog_M_to_Fun = ()


#push-options "--z3rlimit 20 --ifuel 0"
let prog_M_to_Fun_equiv
      opt
      #ek (#a : Type) (t : M.repr ek a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (c : M.prog_cond t.repr_tree pre post)
      (sl0 : M.sl_f pre)
  =
    let { pc_tree = t_M; pc_post_len = post_n; pc_shape = shp_M } = c in
    let t_ST    = ST.repr_ST_of_M t.repr_tree t_M          in
    let shp_ST  = ST.shape_ST_of_M shp_M                   in
    (**) ST.repr_ST_of_M_shape t.repr_tree t_M shp_M;
    let (|t_ST', shp_ST'|)
      : (t : ST.prog_tree a _ _ & s : ST.shape_tree _ _ {ST.prog_has_shape t s}) =
      if opt.o_flatten
      then ((**) ST.flatten_prog_shape t_ST shp_ST;
           (|ST.flatten_prog t_ST, ST.flatten_shape shp_ST|))
      else (|t_ST, shp_ST|)                                in
    let s_ST' = ST.mk_prog_shape t_ST' shp_ST'             in
    let (|t_SF, shp_SF|)
      : (t : SF.prog_tree a _ & s : SF.shape_tree _ {SF.prog_has_shape t s})
      = if opt.o_ST2SF then (
           (**) ST2SF_Spec.repr_SF_of_ST_shape t_ST' s_ST' sl0;
           (|ST2SF_Spec.repr_SF_of_ST_rall t_ST' s_ST' sl0, ST2SF_Spec.shape_SF_of_ST_rall shp_ST'|)
        ) else (
           (**) ST2SF_Base.repr_SF_of_ST_shape t_ST' shp_ST' sl0;
           (|ST2SF_Base.repr_SF_of_ST t_ST' sl0, ST2SF_Base.shape_SF_of_ST shp_ST'|)
        )
    in
    let t_Fun   = SF.repr_Fun_of_SF t_SF                   in
    let shp_Fun = SF.shape_Fun_of_SF shp_SF                in
    (**) SF.repr_Fun_of_SF_shape t_SF (SF.mk_prog_shape t_SF shp_SF);
    let t_Fun' =
      if opt.o_elim_ret
      then Fun.elim_returns SF.sl_tys_lam t_Fun shp_Fun
      else t_Fun
    in

    calc (<==>) {
      M.tree_req t.repr_tree t_M sl0;
    <==> { ST.repr_ST_of_M_req t.repr_tree t_M sl0 }
      ST.tree_req t_ST sl0;
    };// for the ensures we need to expose that [M.tree_req t.repr_tree t_M sl0 ==> ST.tree_req t_ST sl0]
    calc (<==>) {
      ST.tree_req t_ST sl0;
    <==> { ST.flatten_equiv t_ST }
      ST.tree_req t_ST' sl0;
    <==> { if opt.o_ST2SF
         then ST2SF_Spec.repr_SF_of_ST_rall_equiv t_ST' s_ST' sl0
         else ST2SF_Base.repr_SF_of_ST_req t_ST' sl0 }
      SF.tree_req t_SF;
    <==> { SF.repr_Fun_of_SF_req t_SF }
      Fun.tree_req t_Fun;
    };
    calc (<==>) {
      Fun.tree_req t_Fun;
    <==> { if opt.o_elim_ret then Fun.elim_returns_equiv SF.sl_tys_lam t_Fun shp_Fun }
      Fun.tree_req t_Fun';
    };

    introduce M.tree_req t.repr_tree c.pc_tree sl0 ==>
              (forall (x : a) (sl1 : M.sl_f (post x)) .
                (M.tree_ens t.repr_tree t_M sl0 x sl1 <==>
                 Fun.tree_ens (prog_M_to_Fun opt t c sl0) SF.({val_v = x; sel_v = sl1})))
    with _ . introduce forall (x : a) (sl1 : M.sl_f (post x)) . _ with
    begin
      let xsl1 = SF.({val_v = x; sel_v = sl1}) in
      calc (<==>) {
        M.tree_ens t.repr_tree t_M sl0 x sl1;
      <==> { ST.repr_ST_of_M_ens t.repr_tree t_M sl0 x sl1 }
        ST.tree_ens t_ST sl0 x sl1;
      <==> { ST.flatten_equiv t_ST }
        ST.tree_ens t_ST' sl0 x sl1;
      <==> { if opt.o_ST2SF
           then ST2SF_Spec.repr_SF_of_ST_rall_equiv t_ST' s_ST' sl0
           else ST2SF_Base.repr_SF_of_ST_ens t_ST' sl0 x sl1 }
        SF.tree_ens t_SF x sl1;
      <==> { SF.repr_Fun_of_SF_ens t_SF x sl1 }
        Fun.tree_ens t_Fun xsl1;
      <==> { if opt.o_elim_ret then Fun.elim_returns_equiv SF.sl_tys_lam t_Fun shp_Fun }
        Fun.tree_ens t_Fun' xsl1;
      }
    end
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


inline_for_extraction
let __call_repr_steel_0
      (#a : Type)
      (#pre : M.pre_t)     (#post : M.post_t a)
      (#req : M.req_t pre) (#ens  : M.ens_t pre a post)
      (r : M.repr_steel_t SH.KSteel a pre post req ens)
  : SH.unit_steel a (M.vprop_of_list pre) (fun x -> M.vprop_of_list (post x))
      (requires fun h0      -> req (norm_vpl (M.sel_f' pre h0)))
      (ensures  fun h0 x h1 -> ens (norm_vpl (M.sel_f' pre h0)) x (norm_vpl (M.sel_f' (post x) h1)))
  = steel_subcomp_eq
      #a #(M.vprop_of_list pre) #(fun x -> M.vprop_of_list (post x))
      (fun h0 -> req (M.sel pre h0))
      (fun h0 x h1 -> ens (M.sel pre h0) x (M.sel (post x) h1))
      (fun h0 -> req (norm_vpl (M.sel_f' pre h0)))
      (fun h0 x h1 -> ens (norm_vpl (M.sel_f' pre h0)) x (norm_vpl (M.sel_f' (post x) h1)))
      (fun () -> _ by (pointwise (fun () -> try exact (`M.sel_eq') with | _ -> trefl ());
                    norm [delta_only [`%norm_vpl]]; trefl ()))
      (fun () -> _ by (pointwise (fun () -> try exact (`M.sel_eq') with | _ -> trefl ());
                    norm [delta_only [`%norm_vpl]]; trefl ()))
      (SH.FSteel?.f r)

inline_for_extraction
let call_repr_steel #a #pre #post #req #ens r = __call_repr_steel_0 r ()
