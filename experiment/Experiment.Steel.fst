module Experiment.Steel

module SF = Experiment.Steel.Repr.SF

#set-options "--ide_id_info_off --ifuel 0"

let prog_M_to_Fun_equiv
      (#a : Type) (t : M.repr a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (c : M.prog_cond t.repr_tree pre post)
      (sl0 : M.sl_f pre)
  : Lemma (M.tree_req t.repr_tree c.pc_tree sl0 <==> Fun.tree_req (prog_M_to_Fun t c sl0) /\
          (M.tree_req t.repr_tree c.pc_tree sl0 ==>
          (forall (x : a) (sl1 : M.sl_f (post x)) .
               (M.tree_ens t.repr_tree c.pc_tree sl0 x sl1 <==>
                Fun.tree_ens (prog_M_to_Fun t c sl0) SF.({val_v = x; sel_v = sl1})))))
  =
    let { pc_tree = t_M; pc_post_len = post_n; pc_shape = shp_M } = c in
    let t_ST    = ST.repr_ST_of_M t.repr_tree t_M       in
    let shp_ST  = ST.shape_ST_of_M shp_M                in
    (**) ST.repr_ST_of_M_shape t.repr_tree t_M shp_M;
    let t_ST'   = ST.flatten_prog t_ST                  in
    let shp_ST' = ST.flatten_shape shp_ST               in
    (**) ST.flatten_prog_shape t_ST shp_ST;
    let s_ST'   = ST.mk_prog_shape t_ST' shp_ST'        in
    let t_SF    = SF.repr_SF_of_ST_rall t_ST' s_ST' sl0 in
    let t_Fun   = SF.repr_Fun_of_SF t_SF                in

    calc (<==>) {
      M.tree_req t.repr_tree t_M sl0;
    <==> { ST.repr_ST_of_M_req t.repr_tree t_M sl0 }
      ST.tree_req t_ST sl0;
    };// for the ensures we need to expose that [M.tree_req t.repr_tree t_M sl0 ==> ST.tree_req t_ST sl0]
    calc (<==>) {
      ST.tree_req t_ST sl0;
    <==> { ST.flatten_equiv t_ST }
      ST.tree_req t_ST' sl0;
    <==> { SF.repr_SF_of_ST_rall_equiv t_ST' s_ST' sl0 }
      SF.tree_req t_SF;
    <==> { SF.repr_Fun_of_SF_req t_SF }
      Fun.tree_req t_Fun;
    };

    introduce M.tree_req t.repr_tree c.pc_tree sl0 ==>
              (forall (x : a) (sl1 : M.sl_f (post x)) .
                (M.tree_ens t.repr_tree t_M sl0 x sl1 <==>
                 Fun.tree_ens (prog_M_to_Fun t c sl0) SF.({val_v = x; sel_v = sl1})))
    with _ . introduce forall (x : a) (sl1 : M.sl_f (post x)) . _ with
    begin
      calc (<==>) {
        M.tree_ens t.repr_tree t_M sl0 x sl1;
      <==> { ST.repr_ST_of_M_ens t.repr_tree t_M sl0 x sl1 }
        ST.tree_ens t_ST sl0 x sl1;
      <==> { ST.flatten_equiv t_ST }
        ST.tree_ens t_ST' sl0 x sl1;
      <==> { SF.repr_SF_of_ST_rall_equiv t_ST' s_ST' sl0 }
        SF.tree_ens t_SF x sl1;
      <==> { SF.repr_Fun_of_SF_ens t_SF x sl1 }
        Fun.tree_ens t_Fun SF.({val_v = x; sel_v = sl1});
      }
    end


(***** Calling a [M.repr_steel_t] from a Steel program *)

inline_for_extraction
let steel_subcomp_eq
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a)
      (req_f : SE.req_t pre) (ens_f : SE.ens_t pre a post)
      (req_g : SE.req_t pre) (ens_g : SE.ens_t pre a post)
      (pf_req : unit -> squash (req_f == req_g))
      (pf_ens : unit -> squash (ens_f == ens_g))
      (f : M.unit_steel a pre post req_f ens_f)
  : M.unit_steel a pre post req_g ens_g
  = pf_req ();
    pf_ens ();
    U.cast #(M.unit_steel a pre post req_f ens_f) (M.unit_steel a pre post req_g ens_g) f


inline_for_extraction
let __call_repr_steel_0
      (#a : Type)
      (#pre : M.pre_t)     (#post : M.post_t a)
      (#req : M.req_t pre) (#ens  : M.ens_t pre a post)
      (r : M.repr_steel_t a pre post req ens)
  : M.unit_steel a (M.vprop_of_list pre) (fun x -> M.vprop_of_list (post x))
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
      r

inline_for_extraction
let call_repr_steel #a #pre #post #req #ens r = __call_repr_steel_0 r ()


(***** Extracting a [M.unit_steel] from a [M.repr] *)

inline_for_extraction
let steel_of_repr
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      (f : M.repr_steel_t a tr.r_pre tr.r_post tr.r_req tr.r_ens)
  : M.unit_steel a pre post req ens
  =
    tr.r_pre_eq ();
    SE.equiv_can_be_split pre (M.vprop_of_list tr.r_pre);
    introduce forall (x : a) . SE.can_be_split (post x) (M.vprop_of_list (tr.r_post x))
      with (tr.r_post_eq x;
            SE.equiv_can_be_split (post x) (M.vprop_of_list (tr.r_post x)));
    FStar.Classical.forall_intro tr.r_req_eq;
    FStar.Classical.forall_intro_3 tr.r_ens_eq;
    M.unit_steel_subcomp_no_frame
      _ _ req ens
      (tr.r_pre_eq ()) (fun x -> tr.r_post_eq x)
      ()
      f

#push-options "--fuel 1"
let __build_to_repr_t_lem
      (p : SE.vprop) (r_p : M.vprop_list {p `SE.equiv` M.vprop_of_list r_p}) (h : SE.rmem p)
      (v : SE.vprop{SE.can_be_split p v}) (_ : squash (SE.VUnit? v))
      (i : CSl.elem_index (SE.VUnit?._0 v) r_p)
      (i' : int) (_ : squash (i' == i))
  : squash (h v ==
        M.sel r_p (SE.equiv_can_be_split p (M.vprop_of_list r_p);
                   SE.focus_rmem h (M.vprop_of_list r_p)) i)
  =
    SE.equiv_can_be_split p (M.vprop_of_list r_p);
    let h_r = SE.focus_rmem h (M.vprop_of_list r_p) in
    M.vprop_of_list_can_be_split r_p i;
    calc (==) {
      M.sel r_p h_r i;
    == { M.sel_eq' }
      M.sel_f' r_p h_r i;
    == { }
      h_r (SE.VUnit (L.index r_p i));
    == { }
      h v;
    }
#pop-options

#push-options "--ifuel 2"
let __begin_tacs = ()
#pop-options
let __end_tacs = ()
