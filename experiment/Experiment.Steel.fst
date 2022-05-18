module Experiment.Steel

module SF = Experiment.Steel.Repr.SF

#set-options "--ifuel 0"

let prog_M_to_Fun_equiv
      (#a : Type) (t : M.repr a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (c : M.prog_cond t.repr_tree pre post)
      (sl0 : M.sl_t pre)
  : Lemma (M.tree_req t.repr_tree c._1 sl0 <==> Fun.tree_req (prog_M_to_Fun t c sl0) /\
          (M.tree_req t.repr_tree c._1 sl0 ==>
          (forall (x : a) (sl1 : M.sl_t (post x)) .
               (M.tree_ens t.repr_tree c._1 sl0 x sl1 <==>
                Fun.tree_ens (prog_M_to_Fun t c sl0) SF.({val_v = x; sel_v = sl1})))))
  =
    let (|t_M, s_M|) = c in
    let t_ST    = ST.repr_ST_of_M t.repr_tree t_M       in
    let shp_ST  = ST.shape_ST_of_M s_M.shp              in
    (**) ST.repr_ST_of_M_shape t.repr_tree t_M s_M.shp;
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

    introduce M.tree_req t.repr_tree c._1 sl0 ==>
              (forall (x : a) (sl1 : M.sl_t (post x)) .
                (M.tree_ens t.repr_tree t_M sl0 x sl1 <==>
                 Fun.tree_ens (prog_M_to_Fun t c sl0) SF.({val_v = x; sel_v = sl1})))
    with _ . introduce forall (x : a) (sl1 : M.sl_t (post x)) . _ with
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

inline_for_extraction
let prog_M_to_Fun_extract
      (#a : Type) (t : M.repr a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (c : M.prog_cond t.repr_tree pre post)
      (req : M.req_t pre) (ens : M.ens_t pre a post)
      (sub : (sl0 : M.sl_t pre) -> Lemma (requires req sl0)
               (ensures Fun.tree_req (prog_M_to_Fun t c sl0) /\
                  (forall (x : a) (sl1 : M.sl_t (post x)) .
                    Fun.tree_ens (prog_M_to_Fun t c sl0) SF.({val_v = x; sel_v = sl1}) ==> ens sl0 x sl1)))
  : M.repr_steel_t a pre post req ens
  =
    M.repr_steel_subcomp _ _ _ _
      (fun sl0       -> sub sl0; prog_M_to_Fun_equiv t c sl0)
      (fun sl0 x sl1 -> prog_M_to_Fun_equiv t c sl0; sub sl0)
      (t.repr_steel pre post c._1)

inline_for_extraction
let prog_M_to_Fun_extract_wp
      (#a : Type) (t : M.repr a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (c : M.prog_cond t.repr_tree pre post)
      (req : M.req_t pre) (ens : M.ens_t pre a post)
      (wp : (sl0 : M.sl_t pre) -> Lemma
              (Fun.tree_wp (prog_M_to_Fun t c sl0) (fun res -> ens sl0 res.val_v res.sel_v)))
  : M.repr_steel_t a pre post req ens
  = prog_M_to_Fun_extract t c req ens
      (fun sl0 -> wp sl0; Fun.tree_wp_sound (prog_M_to_Fun t c sl0) (fun res -> ens sl0 res.val_v res.sel_v))


(***** Calling a [M.repr_steel_t] from a Steel program *)

type unit_steel (a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
  = unit -> SE.Steel a pre post req ens

inline_for_extraction
let steel_subcomp_eq
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a)
      (req_f : SE.req_t pre) (ens_f : SE.ens_t pre a post)
      (req_g : SE.req_t pre) (ens_g : SE.ens_t pre a post)
      (pf_req : unit -> squash (req_f == req_g))
      (pf_ens : unit -> squash (ens_f == ens_g))
      (f : unit_steel a pre post req_f ens_f)
  : unit_steel a pre post req_g ens_g
  = pf_req ();
    pf_ens ();
    U.cast #(unit_steel a pre post req_f ens_f) (unit_steel a pre post req_g ens_g) f


inline_for_extraction
let __call_repr_steel
      (#a : Type)
      (#pre : M.pre_t)     (#post : M.post_t a)
      (#req : M.req_t pre) (#ens  : M.ens_t pre a post)
      (r : M.repr_steel_t a pre post req ens)
  : unit_steel a (M.vprop_of_list pre) (fun x -> M.vprop_of_list (post x))
      (requires fun h0      -> req (norm_vpl (M.rmem_sels pre h0)))
      (ensures  fun h0 x h1 -> ens (norm_vpl (M.rmem_sels pre h0))
                                x
                                (norm_vpl (M.rmem_sels (post x) h1)))
  = steel_subcomp_eq
      #a #(M.vprop_of_list pre) #(fun x -> M.vprop_of_list (post x))
      (fun h0 -> req (M.rmem_sels pre h0))
      (fun h0 x h1 -> ens (M.rmem_sels pre h0) x (M.rmem_sels (post x) h1))
      (fun h0 -> req (norm_vpl (M.rmem_sels pre h0)))
      (fun h0 x h1 -> ens (norm_vpl (M.rmem_sels pre h0))
                       x
                       (norm_vpl (M.rmem_sels (post x) h1)))
      (fun () -> _ by (norm [delta_only [`%norm_vpl]]; trefl ()))
      (fun () -> _ by (norm [delta_only [`%norm_vpl]]; trefl ()))
      r

inline_for_extraction
let call_repr_steel #a #pre #post #req #ens r = __call_repr_steel r ()
