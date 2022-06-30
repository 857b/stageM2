module Experiment.Steel.Tac.LV

module U    = Learn.Util
module L    = FStar.List.Pure
module M    = Experiment.Steel.Repr.M
module Ll   = Learn.List
module Veq  = Experiment.Steel.VEquiv
module Opt  = Learn.Option
module Perm = Learn.Permutation

open Experiment.Steel.VPropList
open Learn.List.Mask
open Experiment.Steel.Repr.LV
open FStar.Tactics
open Learn.Tactics.Util
open Experiment.Steel.Interface
open Experiment.Steel.Tac


(**** Building a [eq_injection_l] *)

let traverse_partial_injection
      (#a : Type) (src trg : list a)
      (ij : Veq.partial_injection src trg)
  : Lemma (requires Some? (Opt.traverse_list ij))
          (ensures  is_eq_injection src trg (L.index (Some?.v (Opt.traverse_list ij))))
  =
    let ij' = L.index (Some?.v (Opt.traverse_list ij)) in
    Perm.injectiveI ij' (fun i i' ->
      Opt.traverse_list_index ij i;
      Opt.traverse_list_index ij i');
    introduce forall (i : Fin.fin (L.length src)) . L.index trg (ij' i) == L.index src i
      with Opt.traverse_list_index ij i

[@@ __cond_solver__]
let __build_eq_injection_l
      (#a : Type) (src trg : list a)
      (ij0 : Veq.partial_injection src trg)
      (ij1 : list (Fin.fin (L.length trg)))
      (ij1_eq : squash (Some ij1 == Opt.traverse_list ij0))
  : eq_injection_l src trg
  =
    (**) traverse_partial_injection src trg ij0;
    ij1

let __normal_build_eq_injection_l : list norm_step = [
  delta_only [`%L.splitAt; `%L.length; `%Ll.initi; `%len; `%Ll.set;
              `%Opt.traverse_list; `%Opt.map];
  delta_attr [`%__cond_solver__];
  iota; zeta; primops
]

/// Solves a goal [eq_injection_l src trg].
let build_eq_injection_l fr ctx : Tac unit
  =
    let goal = cur_goal () in
    apply_raw (`__build_eq_injection_l);
    // ij0
    build_partial_injection fr ctx;
    // ij1
    dismiss (); //ij1
    norm __normal_build_eq_injection_l;
    cs_try trefl fr ctx (fun m -> fail (m Fail_eq_injection [Info_goal goal]))
    // TODO better error message: show remaining elements

let test_build_eq_injection_l
  : eq_injection_l (String.list_of_string "aabc") (String.list_of_string "faedcab")
  = _ by (norm [primops]; build_eq_injection_l default_flags dummy_ctx)


(**** Building a [Perm.pequiv_list] *)

let eq_injection_pequiv_list
      (#a : Type) (src trg : list a)
      (ij : eq_injection_l src trg)
  : Lemma (requires L.length trg == L.length src)
          (ensures  src == Perm.apply_perm_r (Perm.perm_f_of_list ij) trg)
  = Ll.list_extensionality src (Perm.apply_perm_r (Perm.perm_f_of_list ij) trg) (fun i -> ())

[@@ __cond_solver__]
let __build_pequiv_list
      (#a : Type) (src trg : list a)
      (eq_len : squash L.(length trg == length src))
      (ij : eq_injection_l src trg)
  : Perm.pequiv_list trg src
  =
    (**) eq_injection_pequiv_list src trg ij;
    ij

/// Solves a goal [Perm.pequiv_list l0 l1]
let build_pequiv_list fr ctx : Tac unit
  =
    apply (`__build_pequiv_list);
    // eq_len
    cs_try (fun () ->
      norm [delta_only [`%L.length]; iota; zeta; primops];
      trefl ()
    ) fr ctx (fun m -> fail (m Fail_pequiv_len []));
    // ij
    build_eq_injection_l fr ctx

let test_build_pequiv_list
  : Perm.pequiv_list (String.list_of_string "aabc") (String.list_of_string "caba")
  = _ by (norm [primops]; build_pequiv_list default_flags dummy_ctx)


(*** Building a [lin_cond] *)

let __normal_lc : list norm_step = [
  delta_only [`%L.map; `%L.length; `%L.mem; `%L.op_At; `%L.append; `%L.splitAt; `%L.count; `%L.map2;
              `%Ll.initi; `%Ll.repeat;
              `%Mktuple2?._1; `%Mktuple2?._2];
  delta_attr [`%__tac_helper__; `%__cond_solver__; `%__lin_cond__; `%__mask__];
  iota; zeta; primops
]

let norm_lc () : Tac unit =
  norm __normal_lc


/// Contrary to what is done in [Tac.MCond], were we propagate the [?post] of [M.tree_cond t pre ?post] as a concrete
/// term when it is known, we always call our tactics on goals [lin_cond env t ?csm ?prd] where [?prd] is an uvar.
/// Instead when we have a (possibly partial) constraint on [?prd], we first infer a [lin_cond] then we use [LCsub]
/// to satisfy the constraint. However, the knowledge of the constraints is useful for introducing dependencies in
/// [LCret]. For this reason, we propagate some [prd_hint] in the context.
/// Currently we replicate the behaviour of [Tac.MCond] for the introduction of dependencies.
type prd_hint (#a : Type) (prd : prd_t a) = unit


#push-options "--fuel 0 --ifuel 0"

[@@ __mask__]
unfold
let filter_diff (#a : Type) (#n : nat) (m0 m1 : Ll.vec n bool) (l : Ll.vec n a) : list a
  = filter_mask (mask_diff m0 m1) (filter_mask (mask_not m0) l)

[@@ __cond_solver__]
let pequiv_list_refl (#a : Type) (l : list a)
  : Perm.pequiv_list l l
  = Perm.perm_f_to_list (Perm.pequiv_refl l)

[@@ __cond_solver__]
let lcsub_add_csm
      (env : vprop_list) (#a : Type) (t : M.prog_tree a)
      (csm0 : csm_t env) (prd0 : prd_t a)
      (lc : lin_cond env t csm0 prd0)
      (csm1 : csm_t env) (prd1 : prd_t a)
      (prd1_f : (x : a) -> Perm.pequiv_list L.(prd0 x @ filter_diff csm0 csm1 env) (prd1 x))
  : lin_cond env t (mask_or csm0 csm1) prd1
  =
    let csm' = mask_diff csm0 csm1 in
    (**) mask_comp_or_mask_diff csm0 csm1;
    LCsub env csm0 prd0 lc csm' prd1 prd1_f

/// [LCret] with [prd = sl_hint]
[@@ __cond_solver__]
let __build_LCret
      (env : vprop_list)
      (a : Type u#a) (x : a) (sl_hint : M.post_t a)
      (prd : prd_t a) (prd_h : prd_hint sl_hint -> prd_hint prd)
      (csm_f : eq_injection_l (prd x) env)
  : lin_cond env (M.Tret a x sl_hint) (eij_trg_mask csm_f) prd
  = LCret env #a #x #sl_hint prd csm_f

/// To infer a [Tbind], we first infer the left side [f] then the right side [g] in the resulting environment.
/// In order to use [LCbind], we must ensure that [g] consumes all the [vprop'] produced by [f] (that is, the first
/// part of the resulting environment) and that the other consumed [vprop'] ([g_csm]) and all the variables produced
/// by [g] ([g_prd], which includes the subset of [f_prd] that was not consumed by the first inferred signature)
/// are independent of the bound variable [x].
/// By independence of [g_csm], we mean that the consumption of a [vprop'] cannot depend on [x], the [vprop']
/// themselves are necessarily independent of [x] since they are from [env].
/// We use a [LCsub] on [g] to force the consumption of [f_prd]. The independence is ensured by [eqs].
[@@ __cond_solver__]
let __build_LCbind
      (env : vprop_list)
      (a : Type u#a) (b : Type u#a) (f : M.prog_tree a) (g : (a -> M.prog_tree b))
      (f_csm : csm_t env) (f_prd : prd_t a)
      (cf : lin_cond env f f_csm f_prd)
      (g_csm0 : (x : a) -> csm_t (res_env env f_csm (f_prd x))) (g_prd0 : (x : a) -> prd_t b)
      (cg : (x : a) -> lin_cond (res_env env f_csm (f_prd x)) (g x) (g_csm0 x) (g_prd0 x))
      (g_csm : csm_t (filter_mask (mask_not f_csm) env)) (g_prd : prd_t b)
      (eqs : (x : a) -> squash (
            let n0 = L.length (f_prd x) in
            (**) L.splitAt_length n0 (g_csm0 x);
            let g_csm0_f_prd : Ll.vec n0 bool = (L.splitAt n0 (g_csm0 x))._1 in
            eq2 #(list bool) g_csm (L.splitAt (L.length (f_prd x)) (g_csm0 x))._2 /\
            g_prd == (fun (y : b) -> L.(g_prd0 x y @ filter_mask (mask_not g_csm0_f_prd) (f_prd x)))))
  : lin_cond env (M.Tbind a b f g) (bind_csm env f_csm g_csm) g_prd
  =
    LCbind env #a #b #f #g
      f_csm f_prd cf
      g_csm g_prd
      (fun (x : a) ->
        let env1 = res_env env f_csm (f_prd x) in
        let n0 = L.length (f_prd x)            in
        let n1 = mask_len (mask_not f_csm)     in
        L.splitAt_length n0 (g_csm0 x);
        let g_csm0a, g_csm0b = L.splitAt n0 (g_csm0 x) in
        let g_csm0a : Ll.vec n0 bool = g_csm0a in
        let g_csm0b : Ll.vec n1 bool = g_csm0b in
        Ll.lemma_splitAt_append n0 (g_csm0 x);
        assert (g_csm0 x == L.(g_csm0a @ g_csm0b));

        let g_csm1 = mask_split_l n0 n1 in

        let g_csm_0 = mask_comp_or (g_csm0 x) (mask_diff (g_csm0 x) g_csm1) in
        let g_csm_1 = bind_g_csm' env f_csm (f_prd x) g_csm                 in
        Ll.list_extensionality g_csm_0 g_csm_1
          (fun i ->
            Ll.pat_append ();
            if i >= n0 then begin
              assert (L.index g_csm_0 i == L.index (g_csm0 x) i);
              calc (==) {
                L.index g_csm_1 i;
              == { }
                L.index g_csm (i-n0);
              == { eqs x }
                L.index g_csm0b (i - n0);
              == { L.lemma_splitAt_reindex_right n0 (g_csm0 x) (i - n0) }
                L.index (g_csm0 x) i;
              }
            end);

        (**) mask_comp_or_mask_diff (g_csm0 x) g_csm1;
        lcsub_add_csm env1 (g x) (g_csm0 x) (g_prd0 x) (cg x) g_csm1 g_prd
          (fun (y : b) ->
            calc (==) {
              g_prd y;
            == { eqs x }
              L.(g_prd0 x y @ filter_mask (mask_not g_csm0a) (f_prd x));
            };
            calc (==) {
              filter_diff (g_csm0 x) g_csm1 env1 <: vprop_list;
            == { filter_mask_diff_comm (g_csm0 x) g_csm1 env1 }
              filter_mask (filter_mask g_csm1 (mask_not (g_csm0 x))) (filter_mask g_csm1 env1);
            == { }
              filter_mask (mask_not (filter_mask g_csm1 L.(g_csm0a @ g_csm0b)))
                          (filter_mask g_csm1 L.(f_prd x @ filter_mask (mask_not f_csm) env));
            == { filter_mask_split_l n0 n1 g_csm0a g_csm0b;
                 filter_mask_split_l n0 n1 (f_prd x) (filter_mask (mask_not f_csm) env) }
              filter_mask (mask_not g_csm0a) (f_prd x);
            };
            pequiv_list_refl (g_prd y)))

[@@ __cond_solver__]
let __build_LCbindP
      (env : vprop_list)
      (a : Type u#a) (b : Type u#a) (wp : pure_wp a) (g : a -> M.prog_tree b)
      (csm0 : (x : a) -> csm_t env) (prd0 : (x : a) -> prd_t b)
      (cg : (x : a) -> lin_cond env (g x) (csm0 x) (prd0 x))
      (csm : csm_t env) (prd : prd_t b)
      // Since we use [__defer_sig_unification], it is probably not necessary to do this indirection,
      // but it allows to point the dependency on x in the failure message
      (eqs : (x : a) -> squash (csm == csm0 x /\ prd == prd0 x))
  : lin_cond env (M.TbindP a b wp g) csm prd
  =
    LCbindP env #a #b #wp #g csm prd (fun x -> eqs x; cg x)

/// To infer a [Tif], we first infer independently the two branches (except for the [prd_hint] which allow the
/// production of the [thn] branch to be used as a hint for the [els] branch).
/// In order to use [LCif] we then use a [LCsub] on each branch so that they have the same signature.
/// We use the union ([mask_or]) of the consumed [vprop'] of the two branch.
/// For the produced variables, we requires an equivalence between:
/// - the [vprop'] produced by [thn] concatenated with the [vprop'] of [env] consumed by [els] but not by [thn]
/// - the [vprop'] produced by [els] concatenated with the [vprop'] of [env] consumed by [thn] but not by [els]
/// We arbitrarily choose the first as the production of [LCif] and we use the equivalence to change the signature
/// of [els].
[@@ __cond_solver__]
let __build_LCif
      (env : vprop_list)
      (a : Type u#a) (guard : bool) (thn els : M.prog_tree a)
      (thn_csm : csm_t env) (thn_prd : prd_t a)
      (cthn : lin_cond env thn thn_csm thn_prd)
      (els_csm : csm_t env) (els_prd : prd_t a)
      (cels : prd_hint thn_prd -> lin_cond env els els_csm els_prd)
      (veq : (x : a) -> Perm.pequiv_list L.(els_prd x @ filter_diff els_csm thn_csm env)
                                        L.(thn_prd x @ filter_diff thn_csm els_csm env))
  : lin_cond env (M.Tif a guard thn els)
                 (mask_or thn_csm els_csm) L.(fun x -> thn_prd x @ filter_diff thn_csm els_csm env)
  =
    let prd (x : a) = L.(thn_prd x @ filter_diff thn_csm els_csm env) in
    (**) mask_or_sym thn_csm els_csm;
    LCif env #a #guard #thn #els
         (mask_or thn_csm els_csm) prd
         (lcsub_add_csm env thn thn_csm thn_prd cthn
                        els_csm prd
                        (fun x -> pequiv_list_refl (prd x)))
         (lcsub_add_csm env els els_csm els_prd (cels ())
                        thn_csm prd veq)

/// Just an utility to extract the tactic.
[@@ __cond_solver__]
let __build_LCgen
      (env : vprop_list) (a : Type u#a) (gen_tac : M.gen_tac_t) (gen_c : M.spec_r a -> Type u#(max a 2))
      (_ : extract_term gen_tac)
      (csm : csm_t env) (prd : prd_t a)
      (lc : lin_cond env (M.Tgen a gen_tac gen_c) csm prd)
  : lin_cond env (M.Tgen a gen_tac gen_c) csm prd
  = lc

#pop-options


[@@ __cond_solver__]
let __defer_sig_unification
      (#env : vprop_list) (#a : Type) (#t : M.prog_tree a)
      (#csm0 : csm_t env) (#prd0 : prd_t a)
      (lc : lin_cond env t csm0 prd0)
      (#csm1 : csm_t env) (#prd1 : prd_t a)
      (_ : squash (csm1 == csm0 /\ prd1 == prd0))
  : lin_cond env t csm1 prd1
  = lc

/// The following tactics, [build_* fr prd_hint_b] solve goals of the form [lin_cond env t ?csm ?prd],
/// using an optional hint [prd_hint_b : option binder] which should be a binder of type [prd_hint prd].

let build_LCspec fr (_ : option binder) : Tac unit
  =
    apply (`LCspec);
    // sh
    build_spec_r fr (fun () -> [Info_location "in the spec statement"]);
    // csm_f
    norm_lc ();
    build_eq_injection_l fr (fun () -> [Info_location "before the spec statement"])

let build_LCret fr prd_hint_b : Tac unit
  =
    apply (`__build_LCret);
    // prd_h
    // If we have an hint from the context, we ignore any hint annotated on the return. This is the behaviour of
    // [Tac.MCond]. It should be fine to keep this behaviour here as long as it is only used for introducing
    // dependencies. If it were to be used for smt fallback, since the hint inferred from the context can be
    // partial, it could be better to use the hint annotated on the return if it is non-empty.
    let ret_hint = intro () in
    exact (binder_to_term (Opt.dflt ret_hint prd_hint_b));
    // csm_f
    build_eq_injection_l fr (fun () -> [Info_location "at the return statement"])


let build_LCgen fr prd_hint_b : Tac unit
  =
    apply (`__build_LCgen);
    let gen_tac = extract_term_tac (fun gtc -> unquote #M.gen_tac_t gtc) in
    gen_tac fr

let rec build_LCbind fr prd_hint_b : Tac unit
  =
    apply (`__build_LCbind);
    // cf
    build_lin_cond fr None;
    // cg
    let x = intro () in
    norm_lc ();
    build_lin_cond fr prd_hint_b;
    // [g_csm <- ...], [g_prd <- ...]
    let x = intro () in
    norm_lc ();
    split ();
      let ctx () = [Info_location "in the bind statement"] in
      cs_try trefl fr ctx (fun m -> fail (m (Fail_dependency "csm" x) []));
      cs_try trefl fr ctx (fun m -> fail (m (Fail_dependency "prd" x) []))

and build_LCbindP fr prd_hint_b : Tac unit
  =
    apply (`__build_LCbindP);
    // cg
    let x = intro () in
    build_lin_cond fr prd_hint_b;
    // 
    // [g_csm <- ...], [g_prd <- ...]
    let x = intro () in
    norm_lc ();
    split ();
      let ctx () = [Info_location "in the bindP statement"] in
      cs_try trefl fr ctx (fun m -> fail (m (Fail_dependency "csm" x) []));
      cs_try trefl fr ctx (fun m -> fail (m (Fail_dependency "prd" x) []))

and build_LCif fr prd_hint_b : Tac unit
  =
    apply (`__build_LCif);
    // cthn
    build_lin_cond fr prd_hint_b;
    // cels
    let thn_hint = intro () in
    build_lin_cond fr (Some (Opt.dflt thn_hint prd_hint_b));
    // veq
    let c = intro () in
    norm_lc ();
    build_pequiv_list fr (fun () -> [Info_location "at the end of the if statement"])

and build_lin_cond (fr : flags_record) (prd_hint_b : option binder) : Tac unit
  =
    let build_tac : flags_record -> option binder -> Tac unit =
      let goal = cur_goal () in
      let args = (collect_app goal)._2 in
      let fail_shape () =
        cs_raise fr dummy_ctx (fun m -> fail (m (Fail_goal_shape GShape_lin_cond) [Info_goal goal])) in
      if L.length args <> 5
      then fail_shape ()
      else let hd = (collect_app (L.index args 2)._1)._1 in
      match inspect hd with
      | Tv_FVar fv | Tv_UInst fv _ ->
          let nd = inspect_fv fv in
          match_M_prog_tree fr dummy_ctx nd
            build_LCspec build_LCret build_LCbind build_LCbindP build_LCif build_LCgen
      | r -> fail_shape ()
    in
    // changes [lin_cond env t ?csm0 ?prd0]
    // into [lin_cond env t ?csm1 ?prd1] and [?csm0 = ?csm1 /\ ?prd0 = ?prd1]
    // where [?csm1] and [?prd1] are fresh uvars
    apply (`__defer_sig_unification);
    // solves [lin_cond env t ?csm1 ?prd1], instantiate [?csm1] and [?prd1]
    build_tac fr prd_hint_b;
    // [?csm0 <- csm1], [?prd0 <- prd1]
    norm_lc ();
    split (); trefl (); trefl ()

#push-options "--ifuel 0 --fuel 0"
[@@ __cond_solver__]
let __build_top_lin_cond
      (#a : Type) (t : M.prog_tree a) (pre : M.pre_t) (post : M.post_t a)
      (csm0 : csm_t pre) (prd0 : prd_t a)
      (lc : prd_hint post -> lin_cond pre t csm0 prd0)
      (veq : (x : a) -> Perm.pequiv_list L.(prd0 x @ filter_mask (mask_not csm0) pre) (post x))
  : top_lin_cond t pre post
  =
    (**) Ll.list_extensionality (mask_or csm0 (csm_all pre)) (csm_all pre) (fun i -> ());
    lcsub_add_csm pre t csm0 prd0 (lc ()) (csm_all pre) post
      (fun x ->
        (**) filter_mask_true (mask_diff csm0 (csm_all pre)) (filter_mask (mask_not csm0) pre) (fun i -> ());
        veq x)
#pop-options

/// Solves a goal [top_lin_cond t pre post]
let build_top_lin_cond (fr : flags_record) : Tac unit
  =
    apply (`__build_top_lin_cond);
    // lc
    let prd_hint_b = intro () in
    build_lin_cond fr (Some prd_hint_b);
    // veq
    let x = intro () in
    norm_lc ();
    build_pequiv_list fr (fun () -> [Info_location "at the end of the program"])
