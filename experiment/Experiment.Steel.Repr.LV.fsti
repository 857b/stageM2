module Experiment.Steel.Repr.LV

module U    = Learn.Util
module L    = FStar.List.Pure
module M    = Experiment.Steel.Repr.M
module Ll   = Learn.List
module Fl   = Learn.FList
module Perm = Learn.Permutation

open Learn.List.Mask
open Experiment.Steel.VPropList


irreducible let __lin_cond__ : unit = ()


type csm_t (env : vprop_list) = mask_t env
type prd_t (a : Type) = a -> vprop_list

type req_t (env : vprop_list) = sl_f env -> Type0
type ens_t (env : vprop_list) (a : Type) (prd : prd_t a) = sl_f env -> (x : a) -> sl_f (prd x) -> Type0

[@@ __lin_cond__]
let res_env (env : vprop_list) (csm : csm_t env) (prd : vprop_list) : vprop_list =
  L.(prd @ filter_mask (mask_not csm) env)

let filter_sl
      (#vs : vprop_list) (mask : mask_t vs) (xs : sl_f vs)
  : sl_f (filter_mask mask vs)
  = filter_mask_fl mask (vprop_list_sels_t vs) xs

let res_sel (#env : vprop_list) (sl0 : sl_f env) (csm : csm_t env) (#prd : vprop_list) (sl1 : sl_f prd)
  : sl_f (res_env env csm prd)
  =
    append_vars sl1 (filter_sl (mask_not csm) sl0)


(****** [eq_injection] *)

type eq_injection' (#a : Type) (src trg : list a) =
  Fin.fin (L.length src) -> Fin.fin (L.length trg)
  
let eq_injection_eq (#a : Type) (src trg : list a) (f : eq_injection' src trg) : prop
  = forall (i : Fin.fin (L.length src)) . L.index trg (f i) == L.index src i

let is_eq_injection (#a : Type) (src trg : list a) (f : eq_injection' src trg) : prop
  = Perm.injective f /\ eq_injection_eq src trg f

type eq_injection (#a : Type) (src trg : list a) =
  f : eq_injection' src trg { is_eq_injection src trg f }

type eq_injection_l (#a : Type) (src trg : list a) =
  l : Ll.vec (L.length src) (Fin.fin (L.length trg)) { is_eq_injection src trg (L.index l) }

[@@ __lin_cond__]
let eij_trg_mask_f (#a : Type) (#src #trg : list a) (eij : eq_injection_l src trg) (j : Fin.fin (L.length trg))
  : bool
  = L.mem j eij

[@@ __lin_cond__]
let eij_trg_mask (#a : Type) (#src #trg : list a) (eij : eq_injection_l src trg)
  : Ll.vec (L.length trg) bool
  = Ll.initi 0 (L.length trg) (eij_trg_mask_f eij)

let eij_sl (#src #trg : vprop_list) (eij : eq_injection src trg) (xs : sl_f trg)
  : sl_f src
  = Fl.mk_flist (vprop_list_sels_t src) (fun i -> xs (eij i) <: (L.index src i).t)


let eij_equiv_f (#a : Type) (#src #trg : list a) (eij : eq_injection_l src trg)
                (i : Fin.fin (L.length src))
  : Fin.fin (mask_len (eij_trg_mask eij))
  = let k = L.index eij i in
    L.lemma_index_memP eij i;
    mask_push (eij_trg_mask eij) k

val eij_equiv_injective (#a : Type) (#src #trg : list a) (eij : eq_injection_l src trg)
  : Lemma (Perm.injective (eij_equiv_f eij))

val eij_equiv_surjective (#a : Type) (#src #trg : list a) (eij : eq_injection_l src trg)
  : Lemma (Perm.surjective (eij_equiv_f eij))
  
val eij_equiv_eq (#a : Type) (#src #trg : list a) (eij : eq_injection_l src trg) (i : Fin.fin (L.length src))
  : Lemma (L.index src i == L.index (filter_mask (eij_trg_mask eij) trg) (eij_equiv_f eij i))

val eij_trg_mask_len (#a : Type) (#src #trg : list a) (eij : eq_injection_l src trg)
  : Lemma (mask_len (eij_trg_mask eij) == L.length src)

let eij_equiv (#a : Type) (#src #trg : list a) (eij : eq_injection_l src trg)
  : Perm.pequiv (filter_mask (eij_trg_mask eij) trg) src
  =
    (**) eij_equiv_injective eij;
    (**) eij_trg_mask_len eij;
    (**) let trg' = filter_mask (eij_trg_mask eij) trg in
    let f = Perm.mk_perm_f (L.length trg') (eij_equiv_f eij) in
    (**) Ll.list_extensionality src (Perm.apply_perm_r f trg') (fun i -> eij_equiv_eq eij i);
    f

val extract_eij_equiv
      (#src #trg : vprop_list) (eij : eq_injection_l src trg) (sl : sl_f trg)
  : Lemma (extract_vars (eij_equiv eij) (filter_sl (eij_trg_mask eij) sl) == eij_sl (L.index eij) sl)


(*** [lin_cond] *)

[@@ __lin_cond__]
let bind_g_csm'
      (env : vprop_list)
      (f_csm : csm_t env) (f_prd : vprop_list)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
  : csm_t (res_env env f_csm f_prd)
  = L.(Ll.repeat (length f_prd) true @ g_csm)

[@@ __lin_cond__]
let bind_csm
      (env : vprop_list)
      (f_csm : csm_t env)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
  : csm_t env
  = mask_comp_or f_csm g_csm

val bind_g_csm'_len
      (env : vprop_list)
      (f_csm : csm_t env) (f_prd : vprop_list)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
  : Lemma (mask_len (bind_g_csm' env f_csm f_prd g_csm) == L.length f_prd + mask_len g_csm)
          [SMTPat (mask_len (bind_g_csm' env f_csm f_prd g_csm))]

val bind_g_csm'_or
      (env : vprop_list)
      (f_csm : csm_t env) (f_prd : vprop_list)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
      (csm1  : csm_t (filter_mask (mask_not g_csm) (filter_mask (mask_not f_csm) env)))
  : Lemma (mask_comp_or (bind_g_csm' env f_csm f_prd g_csm) csm1
        == bind_g_csm' env f_csm f_prd (mask_comp_or g_csm csm1))

val filter_bind_csm
      (env : vprop_list)
      (f_csm : csm_t env)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
  : Lemma (eq2 #vprop_list
           (filter_mask (mask_not (bind_csm env f_csm g_csm)) env)
           (filter_mask (mask_not g_csm) (filter_mask (mask_not f_csm) env)))

val filter_sl_bind_csm
      (env : vprop_list)
      (f_csm : csm_t env)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
      (sl : sl_f env)
  : Lemma (filter_bind_csm env f_csm g_csm;
       filter_sl (mask_not (bind_csm env f_csm g_csm)) sl
    == filter_sl (mask_not g_csm) (filter_sl (mask_not f_csm) sl))


val filter_bind_g_csm'
      (env : vprop_list)
      (f_csm : csm_t env) (f_prd : vprop_list)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
  : Lemma (filter_mask (mask_not (bind_g_csm' env f_csm f_prd g_csm)) (res_env env f_csm f_prd)
        == filter_mask (mask_not (bind_csm env f_csm g_csm)) env)

val filter_sl_bind_g_csm'
      (env : vprop_list)
      (f_csm : csm_t env) (f_prd : vprop_list)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
      (sl0 : sl_f f_prd) (sl1 : sl_f (filter_mask (mask_not f_csm) env))
  : Lemma (filter_bind_g_csm' env f_csm f_prd g_csm; filter_bind_csm env f_csm g_csm;
       filter_sl (mask_not (bind_g_csm' env f_csm f_prd g_csm)) (append_vars sl0 sl1)
    == filter_sl (mask_not g_csm) sl1)


(**) private val __end_bind_lem : unit

[@@ __lin_cond__]
let sub_prd
      (env : vprop_list)
      (csm : csm_t env) (prd : vprop_list)
      (csm' : csm_t (filter_mask (mask_not csm) env))
  : vprop_list
  = L.(prd @ filter_mask csm' (filter_mask (mask_not csm) env))

let sub_prd_sl
      (#env : vprop_list) (sl0 : sl_f env)
      (csm  : csm_t env)  (#prd : vprop_list) (sl1 : sl_f prd)
      (csm' : csm_t (filter_mask (mask_not csm) env))
      (#prd' : vprop_list) (prd_f : Perm.pequiv_list (sub_prd env csm prd csm') prd')
  : sl_f prd'
  = extract_vars (Perm.perm_f_of_list prd_f)
                 (append_vars sl1 (filter_sl csm' (filter_sl (mask_not csm) sl0)))


noeq
type lin_cond : 
     (env : vprop_list) ->
     (#a : Type u#a) -> (t : M.prog_tree a) ->
     (csm : csm_t env) -> (prd : prd_t a) ->
     Type u#(max (a+1) 3)
  =
  | LCspec :
      (env : vprop_list) ->
      (#a : Type u#a) -> (#sp : (M.spec_r a -> Type u#(max a 2))) ->
      (s : M.spec_r a) -> (sh : sp s) ->
      (csm_f : eq_injection_l s.spc_pre env) ->
      lin_cond env (M.Tspec a sp) (eij_trg_mask csm_f) s.spc_post
  | LCret :
      (env : vprop_list) ->
      (#a : Type u#a) -> (#x : a) -> (#sl_hint : M.post_t a) ->
      // NOTE: [prd] is redundant since [csm_f] determines its values
      (prd : prd_t a) -> (csm_f : eq_injection_l (prd x) env) ->
      lin_cond env (M.Tret a x sl_hint) (eij_trg_mask csm_f) prd
  | LCbind :
      (env : vprop_list) ->
      (#a : Type u#a) -> (#b : Type u#a) -> (#f : M.prog_tree a) -> (#g : (a -> M.prog_tree b)) ->
      (f_csm : csm_t env) -> (f_prd : prd_t a) ->
      (cf : lin_cond env f f_csm f_prd) ->
      // [g_csm] and [g_prd] are independent of the return value [x : a] of [f]
      (g_csm : csm_t (filter_mask (mask_not f_csm) env)) -> (g_prd : prd_t b) ->
      (cg : ((x : a) ->
        lin_cond (res_env env f_csm (f_prd x)) (g x) (bind_g_csm' env f_csm (f_prd x) g_csm) g_prd)) ->
      lin_cond env (M.Tbind a b f g) (bind_csm env f_csm g_csm) g_prd
  | LCbindP :
      (env : vprop_list) ->
      (#a : Type u#a) -> (#b : Type u#a) -> (#wp : pure_wp a) -> (#g : (a -> M.prog_tree b)) ->
      (csm : csm_t env) -> (prd : prd_t b) ->
      (cg : ((x : a) -> lin_cond env (g x) csm prd)) ->
      lin_cond env (M.TbindP a b wp g) csm prd
  | LCsub :
      (env : vprop_list) -> (#a : Type u#a) -> (#f : M.prog_tree a) ->
      (csm : csm_t env) -> (prd : prd_t a) ->
      (cf : lin_cond env f csm prd) ->
      (csm' : csm_t (filter_mask (mask_not csm) env)) -> (prd' : prd_t a) ->
      (prd_f : ((x : a) -> Perm.pequiv_list (sub_prd env csm (prd x) csm') (prd' x))) ->
      lin_cond env f (bind_csm env csm csm') prd'


unfold
let match_lin_cond
      (#env : vprop_list)
      (#a0 : Type u#a) (#t0 : M.prog_tree a0)
      (#csm0 : csm_t env) (#prd0 : prd_t a0)
      (ct0 : lin_cond env t0 csm0 prd0)
      (r : (a : Type u#a) -> (t : M.prog_tree a) -> (csm : csm_t env) -> (prd : prd_t a) ->
           (ct : lin_cond env t csm prd) -> Type u#r)
      (c_LCspec : (a : Type u#a) ->  (sp : (M.spec_r a -> Type u#(max a 2))) ->
                  (s : M.spec_r a) -> (sh : sp s) ->
                  (csm_f : eq_injection_l s.spc_pre env) ->
                  Pure (r _ _ _ _ (LCspec env #a #sp s sh csm_f))
                       (requires a0 == a /\ t0 == M.Tspec a sp /\
                                 csm0 == eij_trg_mask csm_f /\ prd0 == s.spc_post /\
                                 ct0 == LCspec env #a #sp s sh csm_f)
                       (ensures fun _ -> True))
      (c_LCret  : (a : Type u#a) -> (x : a) -> (sl_hint : M.post_t a) ->
                  (prd : prd_t a) -> (csm_f : eq_injection_l (prd x) env) ->
                  Pure (r _ _ _ _ (LCret env #a #x #sl_hint prd csm_f))
                       (requires a0 == a /\ t0 == M.Tret a x sl_hint /\
                                 csm0 == eij_trg_mask csm_f /\ prd0 == prd /\
                                 ct0 == LCret env #a #x #sl_hint prd csm_f)
                       (ensures fun _ -> True))
      (c_LCbind : (a : Type u#a) -> (b : Type u#a) -> (f : M.prog_tree a) -> (g : (a -> M.prog_tree b)) ->
                  (f_csm : csm_t env) -> (f_prd : prd_t a) ->
                  (cf : lin_cond env f f_csm f_prd {cf << ct0}) ->
                  (g_csm : csm_t (filter_mask (mask_not f_csm) env)) -> (g_prd : prd_t b) ->
                  (cg : ((x : a) ->
                        lin_cond (res_env env f_csm (f_prd x)) (g x)
                                 (bind_g_csm' env f_csm (f_prd x) g_csm) g_prd)
                        {forall (x : a) . {:pattern (cg x)} cg x << ct0}) ->
                  Pure (r _ _ _ _ (LCbind env #a #b #f #g f_csm f_prd cf g_csm g_prd cg))
                       (requires a0 == b /\ t0 == M.Tbind a b f g /\
                                 csm0 == bind_csm env f_csm g_csm /\ prd0 == g_prd /\
                                 ct0 == LCbind env #a #b #f #g f_csm f_prd cf g_csm g_prd cg)
                       (ensures fun _ -> True))
      (c_LCbindP : (a : Type u#a) -> (b : Type u#a) -> (wp : pure_wp a) -> (g : (a -> M.prog_tree b)) ->
                   (csm : csm_t env) -> (prd : prd_t b) ->
                   (cg : ((x : a) -> lin_cond env (g x) csm prd)
                         {forall (x : a) . {:pattern (cg x)} cg x << ct0}) ->
                   Pure (r _ _ _ _ (LCbindP env #a #b #wp #g csm prd cg))
                        (requires a0 == b /\ t0 == M.TbindP a b wp g /\
                                  csm0 == csm /\ prd0 == prd /\
                                  ct0 == LCbindP env #a #b #wp #g csm prd cg)
                        (ensures fun _ -> True))
      (c_LCsub  : (a : Type u#a) -> (f : M.prog_tree a) ->
                  (csm : csm_t env) -> (prd : prd_t a) ->
                  (cf : lin_cond env f csm prd {cf << ct0}) ->
                  (csm' : csm_t (filter_mask (mask_not csm) env)) -> (prd' : prd_t a) ->
                  (prd_f : ((x : a) -> Perm.pequiv_list (sub_prd env csm (prd x) csm') (prd' x))) ->
                  Pure (r _ _ _ _ (LCsub env #a #f csm prd cf csm' prd' prd_f))
                       (requires a0 == a /\ t0 == f /\
                                 csm0 == bind_csm env csm csm' /\ prd0 == prd' /\
                                 ct0 == LCsub env #a #f csm prd cf csm' prd' prd_f)
                       (ensures fun _ -> True))
  : r _ _ _ _ ct0
  = match ct0 as ct returns r _ _ _ _ ct with
  | LCspec  env #a #sp s sh csm_f                         -> c_LCspec  a sp s sh csm_f
  | LCret   env #a #x #sl_hint prd csm_f                  -> c_LCret   a x sl_hint prd csm_f
  | LCbind  env #a #b #f #g f_csm f_prd cf g_csm g_prd cg -> c_LCbind  a b f g f_csm f_prd cf g_csm g_prd cg
  | LCbindP env #a #b #wp #g csm prd cg                   -> c_LCbindP a b wp g csm prd cg
  | LCsub   env #a #f csm prd cf csm' prd' prd_f          -> c_LCsub   a f csm prd cf csm' prd' prd_f


[@@ __lin_cond__]
let csm_all (env : vprop_list) : csm_t env
  = Ll.repeat (L.length env) true

type top_lin_cond (#a : Type) (t : M.prog_tree a) (pre : M.pre_t) (post : M.post_t a)
  = lin_cond pre t (csm_all pre) post


(*** Semantics *)

[@@ strict_on_arguments [5]] (* strict on [ct] *)
let rec tree_req
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a) (#csm : csm_t env) (#prd : prd_t a)
      (ct : lin_cond env t csm prd)
      (sl0 : sl_f env)
  : Tot Type0 (decreases ct)
  = match ct with
  | LCspec env s _ csm_f ->
      s.spc_req (eij_sl (L.index csm_f) sl0)
  | LCret  env #a #x #sl_hint prd csm_f ->
      True
  | LCbind env #a #b #f #g f_csm f_prd cf g_csm g_prd cg ->
      tree_req cf sl0 /\
      (forall (x : a) (sl_itm : sl_f (f_prd x)) .
        tree_ens cf sl0 x sl_itm ==>
        tree_req (cg x) (res_sel sl0 f_csm sl_itm))
  | LCbindP env #a #b #wp #g csm prd cg ->
      wp (fun x -> tree_req (cg x) sl0)
  | LCsub  env #a #f csm prd cf csm' prd' prd_f ->
      tree_req cf sl0

and tree_ens
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a) (#csm : csm_t env) (#prd : prd_t a)
      (ct : lin_cond env t csm prd)
      (sl0 : sl_f env) (res : a) (sl1 : sl_f (prd res))
  : Tot Type0 (decreases ct)
  = match ct with
  | LCspec env s _ csm_f ->
      s.spc_ens (eij_sl (L.index csm_f) sl0) res sl1
  | LCret  env #a #x #sl_hint prd csm_f ->
      res == x /\
      sl1 == eij_sl (L.index csm_f) sl0
  | LCbind env #a #b #f #g f_csm f_prd cf g_csm g_prd cg ->
      (exists (x : a) (sl_itm : sl_f (f_prd x)) .
        tree_ens cf sl0 x sl_itm /\
        tree_ens (cg x) (res_sel sl0 f_csm sl_itm) res sl1)
  | LCbindP env #a #b #wp #g csm prd cg ->
      (exists (x:a) . as_ensures wp x /\ tree_ens (cg x) sl0 res sl1)
  | LCsub  env #a #f csm prd cf csm' prd' prd_f ->
      (exists (sl1' : sl_f (prd res)) . (
        (**) Ll.pat_append ();
        tree_ens cf sl0 res sl1' /\
        sl1 == sub_prd_sl sl0 csm sl1' csm' (prd_f res)))


(***** Equivalence *)

let equiv' (#env : vprop_list) (#a : Type) (#t : M.prog_tree a) (#csm : csm_t env) (#prd : prd_t a)
           (f g : lin_cond env t csm prd)
  : prop
  = (forall (sl0 : sl_f env) .
       tree_req f sl0 <==> tree_req g sl0) /\
    (forall (sl0 : sl_f env) . tree_req f sl0 ==>
      (forall (res : a) (sl1 : sl_f (prd res)) .
        tree_ens f sl0 res sl1 <==> tree_ens g sl0 res sl1))


(*** Pushing [LCsub] to the leaves *)

//[@@ strict_on_arguments [5]] (* strict on [ct] *)
let rec lcsub_at_leaves
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a) (#csm : csm_t env) (#prd : prd_t a)
      (ct : lin_cond env t csm prd)
  : Tot prop (decreases ct)
  = match ct with
  | LCspec _ _ _ _ | LCret _ _ _ | LCsub  _ _ _ (LCspec _ _ _ _) _ _ _ ->
           True
  | LCbind _ #a _ _ cf _ _ cg ->
           lcsub_at_leaves cf /\ (forall (x : a) . lcsub_at_leaves (cg x))
  | LCbindP _ #a _ _ cg ->
           (forall (x : a) . lcsub_at_leaves (cg x))
  | LCsub  _ _ _ _ _ _ _ ->
           False

/// An alias to present a transformation
type lcsubp_tr
      (#env : vprop_list) (#a : Type) (#t : M.prog_tree a) (#csm : csm_t env) (#prd : prd_t a)
      (f : lin_cond env t csm prd)
  = lin_cond env t csm prd


(***** [LCret] *)

#push-options "--ifuel 0 --fuel 0"
[@@ __lin_cond__]
let sub_ret_prd_f'
      (#env   : vprop_list)
      (#prd0  : vprop_list) (csm_f0 : eq_injection_l prd0 env)
      (#csm1  : csm_t (filter_mask (mask_not (eij_trg_mask csm_f0)) env)) (#prd1 : vprop_list)
      (prd_f1 : vequiv_perm (sub_prd env (eij_trg_mask csm_f0) prd0 csm1) prd1)
      (i : Fin.fin (L.length prd1))
  : (j : Fin.fin (L.length env) {L.index env j == L.index prd1 i})
  =
    (**) Ll.pat_append ();
    let n0    = L.length prd0 in
    let ncsm0 = mask_not (eij_trg_mask csm_f0) in
    let k = prd_f1 i in
    (**) assert L.(index (prd0 @ (filter_mask csm1 (filter_mask ncsm0 env))) k == index prd1 i);
    if k < n0
    then begin
      (**) assert L.(index prd0 k == index prd1 i);
      L.index csm_f0 k
    end else begin
      (**) assert L.(index (filter_mask csm1 (filter_mask ncsm0 env)) (k - n0) == index prd1 i);
      (mask_pull ncsm0 (mask_pull csm1 (k - n0)))
    end

val sub_ret_prd_f_eij
      (#env   : vprop_list)
      (#prd0  : vprop_list) (csm_f0 : eq_injection_l prd0 env)
      (#csm1  : csm_t (filter_mask (mask_not (eij_trg_mask csm_f0)) env)) (#prd1 : vprop_list)
      (prd_f1 : vequiv_perm (sub_prd env (eij_trg_mask csm_f0) prd0 csm1) prd1)
  : Lemma (is_eq_injection prd1 env (sub_ret_prd_f' csm_f0 prd_f1))

[@@ __lin_cond__]
let sub_ret_prd_f
      (#env   : vprop_list)
      (#prd0  : vprop_list) (csm_f0 : eq_injection_l prd0 env)
      (#csm1  : csm_t (filter_mask (mask_not (eij_trg_mask csm_f0)) env)) (#prd1 : vprop_list)
      (prd_f1 : vequiv_perm (sub_prd env (eij_trg_mask csm_f0) prd0 csm1) prd1)
  : eq_injection_l prd1 env
  =
    (**) sub_ret_prd_f_eij csm_f0 prd_f1;
    Ll.initi 0 (L.length prd1) (sub_ret_prd_f' csm_f0 prd_f1)
#pop-options

val sub_ret_prd_f_eij_trg_eq
      (#env   : vprop_list)
      (#prd0  : vprop_list) (csm_f0 : eq_injection_l prd0 env)
      (#csm1  : csm_t (filter_mask (mask_not (eij_trg_mask csm_f0)) env)) (#prd1 : vprop_list)
      (prd_f1 : vequiv_perm (sub_prd env (eij_trg_mask csm_f0) prd0 csm1) prd1)
  : Lemma (bind_csm env (eij_trg_mask csm_f0) csm1 == eij_trg_mask (sub_ret_prd_f csm_f0 (prd_f1)))

[@@ __lin_cond__]
let lcsubp_LCret
      (env    : vprop_list) (a : Type u#a) (x : a) (sl_hint : M.post_t a)
      (prd0   : prd_t a) (csm_f0 : eq_injection_l (prd0 x) env)
      (csm1   : csm_t (filter_mask (mask_not (eij_trg_mask csm_f0)) env)) (prd1 : prd_t a)
      (prd_f1 : (x' : a) -> Perm.pequiv_list (sub_prd env (eij_trg_mask csm_f0) (prd0 x') csm1) (prd1 x'))
  : lcsubp_tr (LCsub env _ _ (LCret env #a #x #sl_hint prd0 csm_f0) csm1 prd1 prd_f1)
  =
    let prd_f1' : vequiv_perm (sub_prd env (eij_trg_mask csm_f0) (prd0 x) csm1) (prd1 x)
                = Perm.perm_f_of_list (prd_f1 x) in
    (**) sub_ret_prd_f_eij_trg_eq csm_f0 prd_f1';
    LCret env #a #x #sl_hint prd1 (sub_ret_prd_f csm_f0 prd_f1')


(***** [LCbind] *)

[@@ __lin_cond__]
let sub_bind_csm
      (#env  : vprop_list)
      (f_csm : csm_t env)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
      (csm1  : csm_t (filter_mask (mask_not (bind_csm env f_csm g_csm)) env))
  : csm_t (filter_mask (mask_not f_csm) env)
  = mask_comp_or g_csm csm1

#push-options "--ifuel 0 --fuel 0"
[@@ __lin_cond__]
let lcsubp_LCbind_prd_f
      (#env   : vprop_list) (#b : Type u#a)
      (f_csm  : csm_t env) (f_prd : vprop_list)
      (g_csm  : csm_t (filter_mask (mask_not f_csm) env)) (g_prd : prd_t b)
      (csm1   : csm_t (filter_mask (mask_not (bind_csm env f_csm g_csm)) env)) (prd1 : prd_t b)
      (prd_f1 : (y : b) -> Perm.pequiv_list (sub_prd env (bind_csm env f_csm g_csm) (g_prd y) csm1) (prd1 y))
      (y : b)
  : Perm.pequiv_list
      (sub_prd (res_env env f_csm f_prd) (bind_g_csm' env f_csm f_prd g_csm) (g_prd y) csm1) (prd1 y)  
  =
    (**) filter_bind_g_csm' env f_csm f_prd g_csm;
    U.cast _ (prd_f1 y)

type lcsubp_LCbind_rc_g
      (env : vprop_list)
      (a : Type u#a) (b : Type u#a) (g : a -> M.prog_tree b)
      (f_csm : csm_t env) (f_prd : prd_t a)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env)) (g_prd : prd_t b)
      (cg : (x : a) -> lin_cond (res_env env f_csm (f_prd x)) (g x) (bind_g_csm' env f_csm (f_prd x) g_csm) g_prd)
      (csm1 : csm_t (filter_mask (mask_not (bind_csm env f_csm g_csm)) env)) (prd1 : prd_t b)
      (prd_f1 : (y : b) -> Perm.pequiv_list (sub_prd env (bind_csm env f_csm g_csm) (g_prd y) csm1) (prd1 y))
  = (x : a) -> lcsubp_tr (
       LCsub (res_env env f_csm (f_prd x))
             (bind_g_csm' env f_csm (f_prd x) g_csm) g_prd (cg x)
             csm1 prd1 (lcsubp_LCbind_prd_f f_csm (f_prd x) g_csm g_prd csm1 prd1 prd_f1))

[@@ __lin_cond__]
let lcsubp_LCbind
      (env : vprop_list)
      (a : Type u#a) (b : Type u#a) (f : M.prog_tree a) (g : a -> M.prog_tree b)
      (f_csm : csm_t env) (f_prd : prd_t a)
      (cf : lin_cond env f f_csm f_prd)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env)) (g_prd : prd_t b)
      (cg : (x : a) -> lin_cond (res_env env f_csm (f_prd x)) (g x) (bind_g_csm' env f_csm (f_prd x) g_csm) g_prd)
      (csm1 : csm_t (filter_mask (mask_not (bind_csm env f_csm g_csm)) env)) (prd1 : prd_t b)
      (prd_f1 : (y : b) -> Perm.pequiv_list (sub_prd env (bind_csm env f_csm g_csm) (g_prd y) csm1) (prd1 y))

      (rc_f : lcsubp_tr cf)
      (rc_g : lcsubp_LCbind_rc_g env a b g f_csm f_prd g_csm g_prd cg csm1 prd1 prd_f1)
  : lcsubp_tr (LCsub env _ _ (LCbind env f_csm f_prd cf g_csm g_prd cg) csm1 prd1 prd_f1)
  =
    (**) mask_comp_or_assoc f_csm g_csm csm1;
    LCbind env f_csm f_prd rc_f
       (mask_comp_or g_csm csm1) prd1
       (fun (x : a) ->
         (**) bind_g_csm'_or env f_csm (f_prd x) g_csm csm1;
         rc_g x)
#pop-options


(***** [LCbindP] *)

[@@ __lin_cond__]
let lcsubp_LCbindP
      (env : vprop_list)
      (a : Type u#a) (b : Type u#a) (wp : pure_wp a) (g : a -> M.prog_tree b)
      (csm0 : csm_t env) (prd0 : prd_t b)
      (cg : (x : a) -> lin_cond env (g x) csm0 prd0)
      (csm1 : csm_t (filter_mask (mask_not csm0) env)) (prd1 : prd_t b)
      (prd_f1 : (y : b) -> Perm.pequiv_list (sub_prd env csm0 (prd0 y) csm1) (prd1 y))

      (rc_g : (x : a) -> lcsubp_tr (LCsub env csm0 prd0 (cg x) csm1 prd1 prd_f1))
  : lcsubp_tr (LCsub env _ _ (LCbindP env #a #b #wp #g csm0 prd0 cg) csm1 prd1 prd_f1)
  =
    LCbindP env #a #b #wp #g (bind_csm env csm0 csm1) prd1 rc_g


(***** [LCsub] *)

[@@ __lin_cond__]
let comp_sub_csm
      (#env : vprop_list)
      (csm0 : csm_t env)
      (csm1 : csm_t (filter_mask (mask_not csm0) env))
      (csm2 : csm_t (filter_mask (mask_not (bind_csm env csm0 csm1)) env))
  : csm_t (filter_mask (mask_not csm0) env)
  = mask_comp_or csm1 csm2

let bind_bind_csm
      (#env : vprop_list)
      (csm0 : csm_t env)
      (csm1 : csm_t (filter_mask (mask_not csm0) env))
      (csm2 : csm_t (filter_mask (mask_not (bind_csm env csm0 csm1)) env))
  : Lemma (bind_csm env (bind_csm env csm0 csm1) csm2 == bind_csm env csm0 (comp_sub_csm csm0 csm1 csm2))
          [SMTPat (bind_csm env (bind_csm env csm0 csm1) csm2)]
  = mask_comp_or_assoc csm0 csm1 csm2

#push-options "--ifuel 0 --fuel 0"
[@@ __lin_cond__]
let comp_sub_prd_f
      (#env : vprop_list)
      (#csm0 : csm_t env) (#prd0 : vprop_list)
      (#csm1 : csm_t (filter_mask (mask_not csm0) env)) (#prd1 : vprop_list)
      (#csm2 : csm_t (filter_mask (mask_not (bind_csm env csm0 csm1)) env)) (#prd2 : vprop_list)
      (f1 : Perm.pequiv_list (sub_prd env csm0 prd0 csm1) prd1)
      (f2 : Perm.pequiv_list (sub_prd env (bind_csm env csm0 csm1) prd1 csm2) prd2)
  : Perm.pequiv_list (sub_prd env csm0 prd0 (comp_sub_csm csm0 csm1 csm2)) prd2
  = 
    let f1 : vequiv_perm (sub_prd env csm0 prd0 csm1) prd1 = Perm.perm_f_of_list f1                     in
    let f2 : vequiv_perm (sub_prd env (bind_csm env csm0 csm1) prd1 csm2) prd2 = Perm.perm_f_of_list f2 in
    let env1  = filter_mask (mask_not csm0) env                     in
    let flt1  = filter_mask csm1 env1                               in
    let flt2  = filter_mask csm2 (filter_mask (mask_not csm1) env1) in
    let flt12 = filter_mask (mask_comp_or csm1 csm2) env1           in

    assert (sub_prd env csm0 prd0 csm1 == L.(prd0 @ flt1));
    calc (==) {
      sub_prd env (bind_csm env csm0 csm1) prd1 csm2;
    == { }
      L.(prd1 @ (filter_mask csm2 (filter_mask (mask_not (mask_comp_or csm0 csm1)) env)));
    == { mask_not_comp_or csm0 csm1;
         filter_mask_and (mask_not csm0) (mask_not csm1) env }
      L.(prd1 @ flt2);
    };
    assert (sub_prd env csm0 prd0 (comp_sub_csm csm0 csm1 csm2) == L.(prd0 @ flt12));

    let f1 : vequiv_perm L.(prd0 @ flt1) prd1 = U.cast _ f1 in
    let f2 : vequiv_perm L.(prd1 @ flt2) prd2 = U.cast _ f2 in
    (**) filter_mask_or_append csm1 csm2 env1;
    let eq_flt_or
      : vequiv_perm flt12 L.(flt1 @ flt2)
      = Perm.perm_cast _ (mask_or_pequiv_append csm1 csm2 env1)
    in
    (**) L.append_assoc prd0 flt1 flt2;
    let f3 : vequiv_perm L.(prd0 @ flt1 @ flt2) prd2
      = U.cast _ Perm.(pequiv_trans (pequiv_append f1 (pequiv_refl _)) f2) in
    let f4 : vequiv_perm (sub_prd env csm0 prd0 (comp_sub_csm csm0 csm1 csm2)) prd2
      = U.cast _ Perm.(pequiv_trans (pequiv_append (pequiv_refl prd0) eq_flt_or) f3) in
    Perm.perm_f_to_list f4
#pop-options

[@@ __lin_cond__]
let lcsubp_LCsub
      (env : vprop_list) (a : Type u#a) (f : M.prog_tree a)
      (csm0 : csm_t env) (prd0 : prd_t a)
      (cf : lin_cond env f csm0 prd0)
      (csm1 : csm_t (filter_mask (mask_not csm0) env)) (prd1 : prd_t a)
      (prd_f1 : (x : a) -> Perm.pequiv_list (sub_prd env csm0 (prd0 x) csm1) (prd1 x))
      (csm2 : csm_t (filter_mask (mask_not (bind_csm env csm0 csm1)) env)) (prd2 : prd_t a)
      (prd_f2 : (x : a) -> Perm.pequiv_list (sub_prd env (bind_csm env csm0 csm1) (prd1 x) csm2) (prd2 x))

      (rc_g : lcsubp_tr (LCsub env csm0 prd0 cf (comp_sub_csm csm0 csm1 csm2) prd2
                                    (fun x -> comp_sub_prd_f (prd_f1 x) (prd_f2 x))))
  : lcsubp_tr (LCsub env _ _ (LCsub env csm0 prd0 cf csm1 prd1 prd_f1) csm2 prd2 prd_f2)
  = rc_g

/// We could prove that this transformation yields an equivalent program ([equiv]) but it is not necessary to prove it.
(*
val lcsubp_LCsub
      (#env : vprop_list) (#a : Type u#a) (#f : M.prog_tree a)
      (#csm0 : csm_t env) (#prd0 : prd_t a)
      (cf : lin_cond env f csm0 prd0)
      (csm1 : csm_t (filter_mask (mask_not csm0) env)) (prd1 : prd_t a)
      (prd_f1 : (x : a) -> vequiv_perm (sub_prd env csm0 (prd0 x) csm1) (prd1 x))
      (csm2 : csm_t (filter_mask (mask_not (bind_csm env csm0 csm1)) env)) (prd2 : prd_t a)
      (prd_f2 : (x : a) -> vequiv_perm (sub_prd env (bind_csm env csm0 csm1) (prd1 x) csm2) (prd2 x))
  : equiv'
      (LCsub env _ _ (LCsub env csm0 prd0 cf csm1 prd1 prd_f1) csm2 prd2 prd_f2)
      (LCsub env csm0 prd0 cf (comp_sub_csm csm0 csm1 csm2) prd2 (fun x -> comp_sub_prd_f (prd_f1 x) (prd_f2 x)))
*)

(**** Definition of the transformation *)

(* Since we use F* binders for LCbind, we cannot define a size like this
let rec lin_cond_size
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a) (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond env t csm prd)
  : Tot nat (decreases lc)
  = match lc with
  | LCspec _ _ | LCret  _ _ _ -> 0
  | LCbind _ _ _ cf _ _ cg -> lin_cond_size cf + lin_cond_size cg + 1
  | LCsub  _ _ _ cf _ _ _ -> lin_cond cf + 1
*)

#push-options "--ifuel 1 --fuel 0 --z3rlimit 20"
(**) private val ___begin_lc_sub_push : unit

//[@@ strict_on_arguments [5]] (* strict on [ct] *)
let rec lc_sub_push
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a) (#csm : csm_t env) (#prd : prd_t a)
      (ct : lin_cond env t csm prd)
  : Tot (lcsubp_tr ct) (decreases %[ct; 1])
  = match ct with
  | LCspec _ _ _ _ | LCret  _ _ _ -> ct
  | LCbind env f_csm f_prd cf g_csm g_prd cg ->
      LCbind env f_csm f_prd (lc_sub_push cf) g_csm g_prd (fun x -> lc_sub_push (cg x))
  | LCbindP env #a #b #wp csm0 prd0 cg ->
      LCbindP env #a #b #wp csm0 prd0 (fun x -> lc_sub_push (cg x))
  | LCsub  env csm prd cf csm' prd' prd_f ->
      lc_sub_push_aux cf csm' prd' prd_f

and lc_sub_push_aux
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a) (#csm : csm_t env) (#prd : prd_t a)
      (ct : lin_cond env t csm prd)
      (csm' : csm_t (filter_mask (mask_not csm) env)) (prd' : prd_t a)
      (prd_f : ((x : a) -> Perm.pequiv_list (sub_prd env csm (prd x) csm') (prd' x)))
  : Tot (lcsubp_tr (LCsub env _ _ ct csm' prd' prd_f)) (decreases %[ct; 0])
  = match ct with
  | LCspec _ _ _ _ ->
      LCsub _ _ _ ct csm' prd' prd_f
  | LCret  _ #a #x #sl_hint prd0 csm_f0 ->
      lcsubp_LCret env a x sl_hint prd0 csm_f0 csm' prd'
        (fun (x' : a) -> U.cast #(Perm.pequiv_list (sub_prd env csm (prd x') csm') (prd' x')) _ (prd_f x'))
  | LCbind env #a #b #f #g f_csm f_prd cf g_csm g_prd cg ->
      let csm1 : csm_t (filter_mask (mask_not (bind_csm env f_csm g_csm)) env) = csm' in
      let prd1 : prd_t b = prd' in
      let prd_f1 (y : b) : Perm.pequiv_list (sub_prd env (bind_csm env f_csm g_csm) (g_prd y) csm1) (prd1 y)
             = U.cast _ (prd_f y) in
      let rc_f : lcsubp_tr cf = lc_sub_push cf in
      let rc_g : lcsubp_LCbind_rc_g env a b g f_csm f_prd g_csm g_prd cg csm1 prd1 prd_f1
        = fun (x : a) ->
           let env'   = res_env env f_csm (f_prd x) in
           let g_csm' = bind_g_csm' env f_csm (f_prd x) g_csm in
           let cg   : lin_cond env' (g x) g_csm' g_prd = cg x in
           (**) filter_bind_g_csm' env f_csm (f_prd x) g_csm;
           let csm1 : csm_t (filter_mask (mask_not g_csm') env') = csm1 in
           lc_sub_push_aux
             #env' #b #(g x)
             #g_csm' #g_prd cg
             csm1 prd1
             (lcsubp_LCbind_prd_f f_csm (f_prd x) g_csm g_prd csm1 prd1 prd_f1)
      in
      lcsubp_LCbind env a b f g f_csm f_prd cf g_csm g_prd cg csm1 prd1 prd_f1 rc_f rc_g
  | LCbindP env #a #b #wp #g csm0 prd0 cg ->
      lcsubp_LCbindP env a b wp g csm0 prd0 cg csm' prd' prd_f
        (fun x -> lc_sub_push_aux #env #b #(g x) #csm0 #prd0 (cg x) csm' prd' prd_f)
  | LCsub  env #a #f csm0 prd0 cf csm1 prd1 prd_f1 ->
      let csm2 : csm_t (filter_mask (mask_not (bind_csm env csm0 csm1)) env) = csm' in
      let prd2 : prd_t a = prd' in
      let prd_f2 (x : a) : Perm.pequiv_list (sub_prd env (bind_csm env csm0 csm1) (prd1 x) csm2) (prd2 x)
               = U.cast _ (prd_f x) in
      let prd_f' (x : a) = comp_sub_prd_f (prd_f1 x) (prd_f2 x) in
      let rc : lcsubp_tr (LCsub env csm0 prd0 cf (comp_sub_csm csm0 csm1 csm2) prd2 prd_f')
        = lc_sub_push_aux #env #a #f #csm0 #prd0 cf (comp_sub_csm csm0 csm1 csm2) prd2 prd_f'
      in
      lcsubp_LCsub env a f csm0 prd0 cf csm1 prd1 prd_f1 csm2 prd2 prd_f2 rc
#pop-options


val lc_sub_push_at_leaves
      (env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a) (#csm : csm_t env) (#prd : prd_t a)
      (ct : lin_cond env t csm prd)
  : Lemma (lcsub_at_leaves (lc_sub_push ct))
