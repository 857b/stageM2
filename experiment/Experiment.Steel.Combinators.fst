module Experiment.Steel.Combinators

module U   = Learn.Util
module L   = FStar.List.Pure
module T   = FStar.Tactics
module SE  = Steel.Effect
module SH  = Experiment.Steel.Steel
module Fl  = Learn.FList
module Mem = Steel.Memory
module Veq = Experiment.Steel.VEquiv
module TcS = Experiment.Steel.Tac

open Steel.Effect
open Steel.Effect.Atomic
open Experiment.Steel.Interface
open Experiment.Steel.VPropList
open Experiment.Steel.Repr.M

#push-options "--ifuel 1 --ide_id_info_off"

/// We define a "monad" (which does not satisfy the monad laws) on [M.repr]. 

(****** Call *)

#push-options "--z3rlimit 30"
inline_for_extraction noextract
let repr_of_steel_steel
      (a : Type) (pre : pre_t) (post : post_t a) (ro : vprop_list)
      (req : sl_f pre -> sl_f ro -> Type0) (ens : sl_f pre -> (x : a) -> sl_f (post x) -> sl_f ro -> Type0)
      (tcs : tree_cond_Spec a L.(pre @ ro) (spc_post1 (Mkspec_r pre post ro req ens)))
      ($f : spc_steel_t_steel (Mkspec_r pre post ro req ens))
  : (let c = TCspec #a #(spec_r_exact (Mkspec_r pre post ro req ens)) _ SpecExact tcs in
     repr_steel_t SH.KSteel a tcs.tcs_pre tcs.tcs_post (tree_req _ c) (tree_ens _ c))
  = SH.steel_f (fun () ->
    (**) tcs.tcs_pre_eq.veq_g _;
    (**) elim_vpl_append L.(pre @ ro) tcs.tcs_frame;
    (**) elim_vpl_append pre ro;
    let (x : a) = f () in
    (**) intro_vpl_append (post x) ro;
    (**) intro_vpl_append L.(post x @ ro) tcs.tcs_frame;
    (**) (tcs.tcs_post_eq x).veq_g _;
    Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let repr_of_steel_ghost_steel
      (a : Type) (opened : Mem.inames) (pre : pre_t) (post : post_t a) (ro : vprop_list)
      (req : sl_f pre -> sl_f ro -> Type0) (ens : sl_f pre -> (x : a) -> sl_f (post x) -> sl_f ro -> Type0)
      (tcs : tree_cond_Spec a L.(pre @ ro) (spc_post1 (Mkspec_r pre post ro req ens)))
      ($f : spc_steel_t_ghost opened (Mkspec_r pre post ro req ens))
  : (let c = TCspec #a #(spec_r_exact (Mkspec_r pre post ro req ens)) _ SpecExact tcs in
     repr_steel_t (SH.KGhost opened) a tcs.tcs_pre tcs.tcs_post (tree_req _ c) (tree_ens _ c))
  = SH.ghost_f #opened (fun () ->
    (**) tcs.tcs_pre_eq.veq_g _;
    (**) elim_vpl_append L.(pre @ ro) tcs.tcs_frame;
    (**) elim_vpl_append pre ro;
    let (x : a) = f () in
    (**) intro_vpl_append (post x) ro;
    (**) intro_vpl_append L.(post x @ ro) tcs.tcs_frame;
    (**) (tcs.tcs_post_eq x).veq_g _;
    (**) noop ();
    x)
#pop-options


[@@ __repr_M__]
let tree_of_steel_r (#ek : SH.effect_kind) (#a : Type) (#s : spec_r a) ($f : spc_steel_t ek s)
  : prog_tree a
  = Tspec a (spec_r_exact s)

[@@ __repr_M__]
inline_for_extraction noextract
let repr_of_steel_r
      (#a : Type) (s : spec_r a) ($f : spc_steel_t SH.KSteel s)
  : repr SH.KSteel a
  = {
    repr_tree  = tree_of_steel_r f;
    repr_steel = (fun pre'0 post'0 c ->
                    let TCspec _ _ tcs = c in
                    let Mkspec_r pre0 post0 ro0 req0 ens0 = s in
                    repr_of_steel_steel a pre0 post0 ro0 req0 ens0 tcs (SH.steel_u f))
  }

[@@ __repr_M__]
inline_for_extraction noextract
let repr_of_steel_ghost_r
      (#a : Type) (#opened : Mem.inames) (s : spec_r a) ($f : spc_steel_t (SH.KGhost opened) s)
  : repr (SH.KGhost opened) a
  = {
    repr_tree  = tree_of_steel_r f;
    repr_steel = (fun pre'0 post'0 c ->
                    let TCspec _ _ tcs = c in
                    let Mkspec_r pre0 post0 ro0 req0 ens0 = s in
                    repr_of_steel_ghost_steel a opened pre0 post0 ro0 req0 ens0 tcs (SH.ghost_u f))
  }


[@@ __repr_M__]
let tree_of_steel
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      ($f : SH.unit_steel a pre post req ens)
  : prog_tree a
  = Tspec a (spec_r_steel pre post req ens)

// FIXME? delta_only & delta_attr do not work under a match, but delta_qualifier does
private
let __postprocess_steps : list norm_step = [
  delta_qualifier ["inline_for_extraction"];
  iota
]

//[@@ __repr_M__; FStar.Tactics.(postprocess_with (fun () -> norm __postprocess_steps; trefl ()))]
[@@ __repr_M__]
inline_for_extraction noextract
let repr_of_steel
      (#a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      ($f : SH.unit_steel a pre post req ens)
  : repr SH.KSteel a
  = {
    repr_tree  = tree_of_steel f;
    repr_steel = (fun pre'0 post'0 c ->
                    let TCspec #a #sp s sh tcs = c in
                    let SpecSteel tr (Mkspec_find_ro (Mkspec_r pre0 post0 ro0 req0 ens0)
                                                     pre_eq post_eq req_eq ens_eq)
                      = U.cast (spec_r_steel pre post req ens s) sh in
                    let sr = Mkspec_find_ro (Mkspec_r pre0 post0 ro0 req0 ens0)
                                            pre_eq post_eq req_eq ens_eq in
                    repr_of_steel_steel a pre0 post0 ro0 req0 ens0 tcs
                       (spec_r_of_find_ro sr (repr_steel_of_steel tr f)))
  }

//[@@ __repr_M__; FStar.Tactics.(postprocess_with (fun () -> norm __postprocess_steps; trefl ()))]
[@@ __repr_M__]
inline_for_extraction noextract
let repr_of_steel_ghost
      (#a : Type) (#opened : Mem.inames)
      (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      ($f : SH.unit_steel_ghost a opened pre post req ens)
  : repr (SH.KGhost opened) a
  = {
    repr_tree  = Tspec a (spec_r_steel pre post req ens);
    repr_steel = (fun pre'0 post'0 c ->
                    let TCspec #a #sp s sh tcs = c in
                    let SpecSteel tr (Mkspec_find_ro (Mkspec_r pre0 post0 ro0 req0 ens0)
                                                     pre_eq post_eq req_eq ens_eq)
                      = U.cast (spec_r_steel pre post req ens s) sh in
                    let sr = Mkspec_find_ro (Mkspec_r pre0 post0 ro0 req0 ens0)
                                            pre_eq post_eq req_eq ens_eq in
                    repr_of_steel_ghost_steel a opened pre0 post0 ro0 req0 ens0 tcs
                        (spec_r_of_find_ro_ghost sr (repr_steel_of_steel_ghost tr f)))
  }


(****** Return *)

inline_for_extraction noextract
let return_steel
      (a : Type) (x : a) (sl_hint : post_t a)
      (pre : pre_t) (post : post_t a)
      (e : Veq.vequiv pre (post x))
  : (let c = TCret #a #x #sl_hint pre post e in
     repr_steel_t SH.KSteel a pre post (tree_req _ c) (tree_ens _ c))
  = SH.steel_f (fun () ->
    (**) e.veq_g _;
    Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let return_ghostI_steel
      (a : Type) (opened : Mem.inames) (x : a) (sl_hint : post_t a)
      (pre : pre_t) (post : post_t a)
      (e : Veq.vequiv pre (post x))
  : (let c = TCret #a #x #sl_hint pre post e in
     repr_steel_t (SH.KGhostI opened) a pre post (tree_req _ c) (tree_ens _ c))
  = SH.ghostI_f #opened (fun () ->
    (**) e.veq_g _;
    Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let return_ghost_steel
      (a : Type) (opened : Mem.inames) (x : a) (sl_hint : post_t a)
      (pre : pre_t) (post : post_t a)
      (e : Veq.vequiv pre (post x))
  : (let c = TCret #a #x #sl_hint pre post e in
     repr_steel_t (SH.KGhost opened) a pre post (tree_req _ c) (tree_ens _ c))
  = SH.ghost_f #opened (fun () ->
    (**) e.veq_g _;
    x)


[@@ __repr_M__]
inline_for_extraction noextract
let return_hint (#a : Type) (x : a) (sl_hint : post_t a)
  : repr SH.KSteel a
  = {
    repr_tree  = Tret a x sl_hint;
    repr_steel = (fun pre0 post0 c ->
        let TCret pre post p = c in
        return_steel a x sl_hint pre post p)
  }

[@@ __repr_M__]
inline_for_extraction noextract
let return_ghostI_hint (#a : Type) (#opened : Mem.inames) (x : a) (sl_hint : post_t a)
  : repr (SH.KGhostI opened) a
  = {
    repr_tree  = Tret a x sl_hint;
    repr_steel = (fun pre0 post0 c ->
        let TCret pre post p = c in
        return_ghostI_steel a opened x sl_hint pre post p)
  }

[@@ __repr_M__]
inline_for_extraction noextract
let return_ghost_hint (#a : Type) (#opened : Mem.inames) (x : a) (sl_hint : post_t a)
  : repr (SH.KGhost opened) a
  = {
    repr_tree  = Tret a x sl_hint;
    repr_steel = (fun pre0 post0 c ->
        let TCret pre post p = c in
        return_ghost_steel a opened x sl_hint pre post p)
  }

[@@ __repr_M__]
inline_for_extraction noextract
let return (#a : Type) (x : a) : repr SH.KSteel a
  = return_hint x (fun _ -> [])

[@@ __repr_M__]
inline_for_extraction noextract
let return_ghost (#a : Type) (#opened : Mem.inames) (x : a) : repr (SH.KGhost opened) a
  = return_ghost_hint x (fun _ -> [])


(****** Bind *)

let elim_tree_req_bind (#a #b : Type) (f : prog_tree a) (g : a -> prog_tree b)
      (#pre : pre_t) (#post : post_t b) (#itm : post_t a)
      (cf  : tree_cond f pre itm) (cg : (x:a) -> tree_cond (g x) (itm x) post)
      (sl0 : sl_f pre)
  : Lemma (requires tree_req _ (TCbind #a #b #f #g pre itm post cf cg) sl0)
          (ensures  tree_req f cf sl0 /\
                    (forall (x : a) (sl1 : sl_f (itm x)) .
                      tree_ens f cf sl0 x sl1 ==> tree_req (g x) (cg x) sl1))
  = assert_norm (tree_req _ (TCbind #a #b #f #g pre itm post cf cg) sl0 == (
      tree_req f cf sl0 /\
      (forall (x : a) (sl1 : sl_f (itm x)) .
         tree_ens f cf sl0 x sl1 ==> tree_req (g x) (cg x) sl1)
    ))

let intro_tree_ens_bind (#a #b : Type) (f : prog_tree a) (g : a -> prog_tree b)
      (#pre : pre_t) (#post : post_t b) (#itm : post_t a)
      (cf  : tree_cond f pre itm) (cg : (x:a) -> tree_cond (g x) (itm x) post)
      (sl0 : sl_f pre) (x : a) (sl1 : sl_f (itm x))
      (y : b) (sl2 : t_of (vprop_of_list (post y)))
  : Lemma (requires tree_req f cf sl0 /\
                    tree_ens f cf sl0 x sl1 /\
                    tree_ens (g x) (cg x) sl1 y sl2)
          (ensures  tree_ens _ (TCbind #a #b #f #g pre itm post cf cg) sl0 y sl2)
  = assert_norm (tree_ens _ (TCbind #a #b #f #g pre itm post cf cg) sl0 y sl2 == (
        (exists (x : a) (sl1 : sl_f (itm x)) .
          tree_ens f cf sl0 x sl1 /\
          tree_ens (g x) (cg x) sl1 y sl2)
    ))

[@@FStar.Tactics.(postprocess_with (fun () -> norm __postprocess_steps; trefl ()))]
inline_for_extraction noextract
let bind_steel
      (a : Type) (b : Type) (f : prog_tree a) (g : (a -> prog_tree b))
      (pre : pre_t) (itm : post_t a) (post : post_t b)
      (cf : tree_cond f pre itm) (cg : ((x : a) -> tree_cond (g x) (itm x) post))
      ($rf : repr_steel_t SH.KSteel a pre itm (tree_req f cf) (tree_ens f cf))
      ($rg : (x : a) -> repr_steel_t SH.KSteel b (itm x) post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbind #a #b #f #g pre itm post cf cg in
     repr_steel_t SH.KSteel b pre post (tree_req _ c) (tree_ens _ c))
  = SH.steel_f (fun () ->
    (**) let sl0 = gget (vprop_of_list pre) in
    (**) (elim_tree_req_bind f g cf cg sl0; ());
    let x = SH.steel_u rf () in
    (**) let sl1 = gget (vprop_of_list (itm x)) in
    let y = SH.steel_u (rg x) () in
    (**) let sl2 = gget (vprop_of_list (post y)) in
    (**) (intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2; ());
    Steel.Effect.Atomic.return y)

[@@FStar.Tactics.(postprocess_with (fun () -> norm __postprocess_steps; trefl ()))]
inline_for_extraction noextract
let bind_atomic_ghost_steel
      (a : Type) (b : Type) (opened : Mem.inames) (f : prog_tree a) (g : (a -> prog_tree b))
      (pre : pre_t) (itm : post_t a) (post : post_t b)
      (cf : tree_cond f pre itm) (cg : ((x : a) -> tree_cond (g x) (itm x) post))
      ($rf : repr_steel_t (SH.KAtomic opened) a pre itm (tree_req f cf) (tree_ens f cf))
      ($rg : (x : a) ->
             repr_steel_t (SH.KGhostI opened) b (itm x) post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbind #a #b #f #g pre itm post cf cg in
     repr_steel_t (SH.KAtomic opened) b pre post (tree_req _ c) (tree_ens _ c))
  = SH.atomic_f (fun () ->
    (**) let sl0 = gget (vprop_of_list pre) in
    (**) (elim_tree_req_bind f g cf cg sl0; ());
    let x = SH.atomic_u rf () in
    (**) let sl1 = gget (vprop_of_list (itm x)) in
    let y = SH.ghostI_u (rg x) () in
    (**) let sl2 = gget (vprop_of_list (post y)) in
    (**) (intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2; ());
    Steel.Effect.Atomic.return y)

[@@FStar.Tactics.(postprocess_with (fun () -> norm __postprocess_steps; trefl ()))]
inline_for_extraction noextract
let bind_ghost_atomic_steel
      (a : Type) (b : Type) (opened : Mem.inames) (f : prog_tree a) (g : (a -> prog_tree b))
      (pre : pre_t) (itm : post_t a) (post : post_t b)
      (cf : tree_cond f pre itm) (cg : ((x : a) -> tree_cond (g x) (itm x) post))
      ($rf : repr_steel_t (SH.KGhostI opened) a pre itm (tree_req f cf) (tree_ens f cf))
      ($rg : (x : a) ->
             repr_steel_t (SH.KAtomic opened) b (itm x) post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbind #a #b #f #g pre itm post cf cg in
     repr_steel_t (SH.KAtomic opened) b pre post (tree_req _ c) (tree_ens _ c))
  = SH.atomic_f (fun () ->
    (**) let sl0 = gget (vprop_of_list pre) in
    (**) (elim_tree_req_bind f g cf cg sl0; ());
    let x = SH.ghostI_u rf () in
    (**) let sl1 = gget (vprop_of_list (itm x)) in
    let y = SH.atomic_u (rg x) () in
    (**) let sl2 = gget (vprop_of_list (post y)) in
    (**) (intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2; ());
    Steel.Effect.Atomic.return y)

[@@FStar.Tactics.(postprocess_with (fun () -> norm __postprocess_steps; trefl ()))]
inline_for_extraction noextract
let bind_ghostI_steel
      (a : Type) (b : Type) (opened : Mem.inames) (f : prog_tree a) (g : (a -> prog_tree b))
      (pre : pre_t) (itm : post_t a) (post : post_t b)
      (cf : tree_cond f pre itm) (cg : ((x : a) -> tree_cond (g x) (itm x) post))
      ($rf : repr_steel_t (SH.KGhostI opened) a pre itm (tree_req f cf) (tree_ens f cf))
      ($rg : (x : a) ->
             repr_steel_t (SH.KGhostI opened) b (itm x) post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbind #a #b #f #g pre itm post cf cg in
     repr_steel_t (SH.KGhostI opened) b pre post (tree_req _ c) (tree_ens _ c))
  = SH.ghostI_f #opened (fun () ->
    (**) let sl0 = gget (vprop_of_list pre) in
    (**) (elim_tree_req_bind f g cf cg sl0; ());
    let x = SH.ghostI_u rf () in
    (**) let sl1 = gget (vprop_of_list (itm x)) in
    let y = SH.ghostI_u (rg x) () in
    (**) let sl2 = gget (vprop_of_list (post y)) in
    (**) (intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2; ());
    Steel.Effect.Atomic.return y)

[@@FStar.Tactics.(postprocess_with (fun () -> norm __postprocess_steps; trefl ()))]
inline_for_extraction noextract
let bind_ghost_steel
      (a : Type) (b : Type) (opened : Mem.inames) (f : prog_tree a) (g : (a -> prog_tree b))
      (pre : pre_t) (itm : post_t a) (post : post_t b)
      (cf : tree_cond f pre itm) (cg : ((x : a) -> tree_cond (g x) (itm x) post))
      ($rf : repr_steel_t (SH.KGhost opened) a pre itm (tree_req f cf) (tree_ens f cf))
      ($rg : (x : a) -> repr_steel_t (SH.KGhost opened) b (itm x) post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbind #a #b #f #g pre itm post cf cg in
     repr_steel_t (SH.KGhost opened) b pre post (tree_req _ c) (tree_ens _ c))
  = SH.ghost_f #opened (fun () ->
    (**) let sl0 = gget (vprop_of_list pre) in
    (**) (elim_tree_req_bind f g cf cg sl0; ());
    let x = SH.ghost_u rf () in
    (**) let sl1 = gget (vprop_of_list (itm x)) in
    let y = SH.ghost_u (rg x) () in
    (**) let sl2 = gget (vprop_of_list (post y)) in
    (**) (intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2; ());
    (**) noop ();
    y)


[@@ __repr_M__]
inline_for_extraction noextract
let bind_ek (#a #b : Type) (ek0 ek1 ek2 : SH.effect_kind)
      (s : (a : Type) -> (b : Type) -> (f : prog_tree a) -> (g : (a -> prog_tree b)) ->
           (pre : pre_t) -> (itm : post_t a) -> (post : post_t b) ->
           (cf : tree_cond f pre itm) -> (cg : ((x : a) -> tree_cond (g x) (itm x) post)) ->
           (rf : repr_steel_t ek0 a pre itm (tree_req f cf) (tree_ens f cf)) ->
           (rg : ((x : a) -> repr_steel_t ek1 b (itm x) post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))) ->
           (let c = TCbind #a #b #f #g pre itm post cf cg in
            repr_steel_t ek2 b pre post (tree_req _ c) (tree_ens _ c)))
      (f : repr ek0 a) (g : a -> repr ek1 b)
  : repr ek2 b
  = {
    repr_tree  = Tbind a b f.repr_tree (fun x -> (g x).repr_tree);
    repr_steel = (fun pre0 post0 c ->
                    let (TCbind #a' #b' #tf #tg pre itm post cf cg) = c in
                    let rg (x : a) : repr_steel_t ek1 b (itm x) post _ _
                                   = (g x).repr_steel _ _ (cg x) in
                    s a b tf tg pre itm post cf cg (f.repr_steel _ _ cf) rg)
  }

[@@ __repr_M__]
inline_for_extraction noextract
let bind (#a #b : Type) (f : repr SH.KSteel a) (g : a -> repr SH.KSteel b)
  : repr SH.KSteel b
  = bind_ek SH.KSteel SH.KSteel SH.KSteel
      (fun a b f g pre itm post cf cg rf rg -> bind_steel a b f g pre itm post cf cg rf rg)
      f g

[@@ __repr_M__]
inline_for_extraction noextract
let bind_ghost (#a #b : Type) (#opened : Mem.inames)
               (f : repr (SH.KGhost opened) a) (g : a -> repr (SH.KGhost opened) b)
  : repr (SH.KGhost opened) b
  = bind_ek (SH.KGhost opened) (SH.KGhost opened) (SH.KGhost opened)
      (fun a b f g pre itm post cf cg rf rg -> bind_ghost_steel a b opened f g pre itm post cf cg rf rg)
      f g


(****** Bind pure *)

inline_for_extraction noextract
let bindP_steel
      (a : Type) (b : Type) (wp : pure_wp a) ($f : unit -> PURE a wp) (g : (a -> prog_tree b))
      (pre : pre_t) (post : post_t b)
      (cg : ((x : a) -> tree_cond (g x) pre post))
      (rg : (x : a) -> repr_steel_t SH.KSteel b pre post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbindP #a #b #wp #g pre post cg in
     repr_steel_t SH.KSteel b pre post (tree_req _ c) (tree_ens _ c))
  = 
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    SH.steel_f (fun () ->
    let x = f () in
    SH.steel_u (rg x) ())

inline_for_extraction noextract
let bindP_atomic_steel
      (a : Type) (b : Type) (opened : Mem.inames) (wp : pure_wp a) ($f : unit -> PURE a wp) (g : (a -> prog_tree b))
      (pre : pre_t) (post : post_t b)
      (cg : ((x : a) -> tree_cond (g x) pre post))
      (rg : (x : a) -> repr_steel_t (SH.KAtomic opened)  b pre post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbindP #a #b #wp #g pre post cg in
     repr_steel_t (SH.KAtomic opened) b pre post (tree_req _ c) (tree_ens _ c))
  = 
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    SH.atomic_f (fun () ->
    let x = f () in
    SH.atomic_u (rg x) ())

inline_for_extraction noextract
let bindP_ghostI_steel
      (a : Type) (b : Type) (opened : Mem.inames) (wp : pure_wp a) ($f : unit -> PURE a wp) (g : (a -> prog_tree b))
      (pre : pre_t) (post : post_t b)
      (cg : ((x : a) -> tree_cond (g x) pre post))
      ($rg : (x : a) -> repr_steel_t (SH.KGhostI opened)  b pre post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbindP #a #b #wp #g pre post cg in
     repr_steel_t (SH.KGhostI opened) b pre post (tree_req _ c) (tree_ens _ c))
  = 
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    SH.ghostI_f (fun () ->
    let x = f () in
    SH.ghostI_u (rg x) ())

inline_for_extraction noextract
let bindP_ghost_steel0
      (a : Type) (b : Type) (opened : Mem.inames) (wp : pure_wp a) ($f : unit -> PURE a wp) (g : (a -> prog_tree b))
      (pre : pre_t) (post : post_t b)
      (cg : ((x : a) -> tree_cond (g x) pre post))
      (rg : (x : a) -> repr_steel_t (SH.KGhost opened) b pre post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbindP #a #b #wp #g pre post cg in
     repr_steel_t (SH.KGhost opened) b pre post (tree_req _ c) (tree_ens _ c))
  =
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    SH.ghost_f #opened (fun () ->
    let x = f () in
    SH.ghost_u (rg x) ())

inline_for_extraction noextract
let bindP_ghost_steel
      (a : Type) (b : Type) (opened : Mem.inames) (wp : pure_wp a) ($f : unit -> GHOST a wp) (g : (a -> prog_tree b))
      (pre : pre_t) (post : post_t b)
      (cg : ((x : a) -> tree_cond (g x) pre post))
      (rg : (x : a) -> repr_steel_t (SH.KGhost opened) b pre post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbindP #a #b #wp #g pre post cg in
     repr_steel_t (SH.KGhost opened) b pre post (tree_req _ c) (tree_ens _ c))
  =
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    SH.ghost_f #opened (fun () ->
    let x = f () in
    SH.ghost_u (rg x) ())

#push-options "--ifuel 1 --fuel 1 --z3rlimit 10"
[@@ __repr_M__]
inline_for_extraction noextract
let bindP_ek (#a #b : Type) (ek : SH.effect_kind) (wp : pure_wp a) ($f : unit -> PURE a wp) (g : a -> repr ek b)
  : repr ek b
  = {
    repr_tree  = TbindP a b wp (fun x -> (g x).repr_tree);
    repr_steel = (fun pre0 post0 c ->
                    let (TCbindP #a' #b' #wp #tg pre post cg) = c in
                    let rg (x : a) : repr_steel_t ek b pre post _ _
                                   = (g x).repr_steel _ _ (cg x) in
                    match ek returns repr_steel_t ek b _ _ _ _ with
                    | SH.KSteel    -> bindP_steel        a b   wp f tg pre post cg rg
                    | SH.KAtomic o -> bindP_atomic_steel a b o wp f tg pre post cg rg
                    | SH.KGhostI o -> bindP_ghostI_steel a b o wp f tg pre post cg rg
                    | SH.KGhost  o -> bindP_ghost_steel0 a b o wp f tg pre post cg rg
                 )
  }

[@@ __repr_M__]
inline_for_extraction noextract
let bindP (#a #b : Type) (wp : pure_wp a) ($f : unit -> PURE a wp) (g : a -> repr SH.KSteel b)
  : repr SH.KSteel b
  = bindP_ek SH.KSteel wp f g

[@@ __repr_M__]
inline_for_extraction noextract
let bindP_ghost (#a #b : Type) (#opened : Mem.inames)
                (wp : pure_wp a) ($f : unit -> GHOST a wp) (g : a -> repr (SH.KGhost opened) b)
  : repr (SH.KGhost opened) b
  = {
    repr_tree  = TbindP a b wp (fun x -> (g x).repr_tree);
    repr_steel = (fun pre0 post0 c ->
                    let (TCbindP #a' #b' #wp #tg pre post cg) = c in
                    let rg (x : a) : repr_steel_t (SH.KGhost opened) b pre post _ _
                                   = (g x).repr_steel _ _ (cg x) in
                    bindP_ghost_steel a b opened wp f tg pre post cg rg)
  }


(****** If-then-else *)

inline_for_extraction noextract
let ite_steel
      (a : Type) (guard : bool) (thn : prog_tree a) (els : prog_tree a)
      (pre : pre_t) (post : post_t a)
      (cthn : tree_cond thn pre post) (cels : tree_cond els pre post)
      ($rthn : repr_steel_t SH.KSteel a pre post (tree_req thn cthn) (tree_ens thn cthn))
      ($rels : repr_steel_t SH.KSteel a pre post (tree_req els cels) (tree_ens els cels))
  : (let c = TCif #a #guard #thn #els pre post cthn cels in
     repr_steel_t SH.KSteel a pre post (tree_req _ c) (tree_ens _ c))
  = SH.steel_f (fun () ->
    if guard then SH.steel_u rthn () else SH.steel_u rels ())

inline_for_extraction noextract
let ite_ghost_steel
      (a : Type) (opened : Mem.inames) (guard : bool) (thn : prog_tree a) (els : prog_tree a)
      (pre : pre_t) (post : post_t a)
      (cthn : tree_cond thn pre post) (cels : tree_cond els pre post)
      ($rthn : repr_steel_t (SH.KGhost opened) a pre post (tree_req thn cthn) (tree_ens thn cthn))
      ($rels : repr_steel_t (SH.KGhost opened) a pre post (tree_req els cels) (tree_ens els cels))
  : (let c = TCif #a #guard #thn #els pre post cthn cels in
     repr_steel_t (SH.KGhost opened) a pre post (tree_req _ c) (tree_ens _ c))
  = SH.ghost_f #opened (fun () ->
    if guard then SH.ghost_u rthn () else SH.ghost_u rels ())


[@@ __repr_M__]
inline_for_extraction noextract
let ite (#a : Type) (guard : bool) (thn els : repr SH.KSteel a)
  : repr SH.KSteel a
  = {
    repr_tree  = Tif a guard thn.repr_tree els.repr_tree;
    repr_steel = (fun pre0 post0 c ->
                    let TCif pre post cthn cels = c in
                    ite_steel a guard _ _ pre post cthn cels
                       (thn.repr_steel _ _ cthn) (els.repr_steel _ _ cels))
  }

[@@ __repr_M__]
inline_for_extraction noextract
let ite_ghost (#a : Type) (#opened : Mem.inames) (guard : bool) (thn els : repr (SH.KGhost opened) a)
  : repr (SH.KGhost opened) a
  = {
    repr_tree  = Tif a guard thn.repr_tree els.repr_tree;
    repr_steel = (fun pre0 post0 c ->
                    let (TCif pre post cthn cels) = c in
                    ite_ghost_steel a opened guard _ _ pre post cthn cels
                       (thn.repr_steel _ _ cthn) (els.repr_steel _ _ cels))
  }



(*** Lifts *)

(***** [erasable_t] *)

type revealed_value (#a : Type) (x : Ghost.erased a) =
  x' : a { x' == Ghost.reveal x }

noeq inline_for_extraction noextract
type erasable_t (a : Type) = {
  erasable_rv : (x : Ghost.erased a) -> revealed_value x
}

private
let __build_revealed_value (a : Type) : (x : Ghost.erased a) -> GTot (revealed_value x)
  = fun x -> Ghost.reveal x

/// Solves a goal [erasable_t a] if a is an erasable type.
let build_erasable_t fr ctx : T.Tac unit
  = T.(
    let a : term
      = match inspect (cur_goal ()) with
        | Tv_App  _ arg -> arg._1
        | _ -> fail "build_erasable_t : goal"
    in
    apply (`Mkerasable_t);
    // The following requires a conversion from [_ -> GTot (revealed_value x)] to [_ -> Tot (revealed_value x)]
    // which succeeds iff [revealed_value x] (i.e. [a]) is erasable.
    // Since we use (`#a), this may generate some guards to retypecheck (`#a).
    with_policy SMT (fun () -> TcS.cs_try (fun () ->
      exact (`(__build_revealed_value (`#a) <: _ -> Tot _)))
    fr ctx (fun m -> fail (m (Fail_not_erasable a) [])))
  )

private
let test_erasable_unit : erasable_t unit
  = _ by (build_erasable_t default_flags TcS.dummy_ctx)

private
let test_erasable_unit' : erasable_t U.unit'
  = _ by (build_erasable_t default_flags TcS.dummy_ctx)

#push-options "--silent"
[@@ expect_failure [228]]
private
let test_erasable_int : erasable_t int
  = _ by (build_erasable_t default_flags TcS.dummy_ctx)
#pop-options

[@@ erasable]
private noeq
type test_guard_type (_ : squash (forall (n : nat) . n >= 0)) =

private
let test_erasable_guard : erasable_t (test_guard_type ())
  = _ by (build_erasable_t default_flags TcS.dummy_ctx)


(***** [steel_liftable] *)

// named as in Coq
noeq
type clos_refl_trans_1n (#a : Type) (r : a -> a -> Type) (x : a) : a -> Type =
  | Rt1n_refl  : clos_refl_trans_1n r x x
  | Rt1n_trans : (y : a) -> (z : a) ->
                 r x y -> clos_refl_trans_1n r y z -> clos_refl_trans_1n r x z

noeq
type steel_liftable1 (a : Type) : SH.effect_kind -> SH.effect_kind -> Type =
  | Lift_ghost_ghostI  : erasable_t a -> (opened : Mem.inames) ->
                         steel_liftable1 a (SH.KGhost     opened) (SH.KGhostI opened)
  | Lift_ghostI_atomic : (opened : Mem.inames) ->
                         steel_liftable1 a (SH.KGhostI    opened) (SH.KAtomic opened)
  | Lift_atomic_steel  : steel_liftable1 a (SH.KAtomic Set.empty)  SH.KSteel

type steel_liftable (a : Type) : SH.effect_kind -> SH.effect_kind -> Type
  = clos_refl_trans_1n (steel_liftable1 a)


/// We define the lift on [repr_steel_t] rather than on [SH.steel] because the latter option does not work
/// with steel's tactic because of the abstract specifications.

let repr_steel_lift_ghost_ghostI_aux
      #a #pre #post #req #ens #opened (f : repr_steel_t (SH.KGhost opened) a pre post req ens)
  : SH.unit_steel_ghost (Ghost.erased a) opened
      (vprop_of_list pre) (fun x -> vprop_of_list (post (Ghost.reveal x)))
      (fun h0 -> req (sel_f pre h0))
      (fun h0 x h1 -> ens (sel_f pre h0) (Ghost.reveal x) (sel_f (post (Ghost.reveal x)) h1))
  =
    fun () ->
      let x = SH.ghost_u f () in
      Ghost.hide x

inline_for_extraction noextract
let repr_steel_lift_ghost_ghostI
      #a #pre #post #req #ens opened (e : erasable_t a) (f : repr_steel_t (SH.KGhost opened) a pre post req ens)
  : repr_steel_t (SH.KGhostI opened) a pre post req ens
  =
    SH.ghostI_f (fun () ->
      let x : Ghost.erased a = repr_steel_lift_ghost_ghostI_aux f () in
      let x' : a = e.erasable_rv x in
      change_equal_slprop (vprop_of_list (post (Ghost.reveal x))) (vprop_of_list (post x'));
      Steel.Effect.Atomic.return x'
  )

inline_for_extraction noextract
let repr_steel_lift_ghostI_atomic
      #a #pre #post #req #ens opened (f : repr_steel_t (SH.KGhostI opened) a pre post req ens)
  : repr_steel_t (SH.KAtomic opened) a pre post req ens
  = SH.atomic_f (fun () -> SH.ghostI_u f ())

inline_for_extraction noextract
let repr_steel_lift_atomic_steel
      #a #pre #post #req #ens (f : repr_steel_t (SH.KAtomic Set.empty) a pre post req ens)
  : repr_steel_t SH.KSteel a pre post req ens
  = SH.steel_f (fun () -> SH.atomic_u f ())

inline_for_extraction noextract
let repr_steel_lift1
      (#a : Type) (#pre : pre_t) (#post : post_t a) (#req : req_t pre) (#ens : ens_t pre a post)
      (#ek0 #ek1 : SH.effect_kind) (l : steel_liftable1 a ek0 ek1)
      (f : repr_steel_t ek0 a pre post req ens)
  : repr_steel_t ek1 a pre post req ens
  = match l with
  | Lift_ghost_ghostI e o -> repr_steel_lift_ghost_ghostI  o e f
  | Lift_ghostI_atomic  o -> repr_steel_lift_ghostI_atomic o   f
  | Lift_atomic_steel     -> repr_steel_lift_atomic_steel      f

inline_for_extraction noextract
let rec repr_steel_lift
      (#a : Type) (#pre : pre_t) (#post : post_t a) (#req : req_t pre) (#ens : ens_t pre a post)
      (#ek0 #ek1 : SH.effect_kind) (l : steel_liftable a ek0 ek1)
      (f : repr_steel_t ek0 a pre post req ens)
  : Tot (repr_steel_t ek1 a pre post req ens) (decreases l)
  = match l with
  | Rt1n_refl -> f
  | Rt1n_trans _ _ l0 l1 -> repr_steel_lift l1 (repr_steel_lift1 l0 f)

[@@ __repr_M__]
inline_for_extraction noextract
let repr_lift
      (#a : Type) (#ek0 #ek1 : SH.effect_kind) (l : steel_liftable a ek0 ek1) (r : repr ek0 a)
  : repr ek1 a
  = { r with repr_steel = (fun pre post c -> repr_steel_lift l (r.repr_steel pre post c)) }


(****** SteelGhost to Steel (Monad) *)

inline_for_extraction noextract
let ghost_to_steel_steel (a : Type) (t : prog_tree (Ghost.erased a)) (pre : pre_t) (post : post_t (Ghost.erased a))
      (c : tree_cond t pre post)
      ($r : repr_steel_t (SH.KGhost Set.empty) (Ghost.erased a) pre post (tree_req t c) (tree_ens t c))
  : repr_steel_t SH.KSteel (Ghost.erased a) pre post (tree_req t c) (tree_ens t c)
  = SH.steel_f (SH.ghost_u r)

[@@ __repr_M__]
inline_for_extraction noextract
let ghost_to_steel (#a : Type) (f : repr (SH.KGhost Set.empty) (Ghost.erased a))
  : repr SH.KSteel (Ghost.erased a)
  = {
    repr_tree  = f.repr_tree;
    repr_steel = (fun pre post c ->
                    ghost_to_steel_steel a f.repr_tree pre post c (f.repr_steel _ _ c))
  }

[@@ __repr_M__]
inline_for_extraction noextract
let ghost_to_steel_ct (#a : Type) (f : repr (SH.KGhost Set.empty) a)
      (rv : (x : Ghost.erased a) -> (x' : a { x' == Ghost.reveal x }))
  : repr SH.KSteel a
  = repr_lift (Rt1n_trans _ _ (Lift_ghost_ghostI ({erasable_rv = rv}) _)
              (Rt1n_trans _ _ (Lift_ghostI_atomic _)
              (Rt1n_trans _ _ Lift_atomic_steel Rt1n_refl))) f
