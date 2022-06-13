module Experiment.Steel.Combinators

module L   = FStar.List.Pure
module SE  = Steel.Effect
module SH  = Experiment.Steel.Steel
module Mem = Steel.Memory
module Veq = Experiment.Steel.VEquiv

open Steel.Effect
open Steel.Effect.Atomic
open Experiment.Steel.VPropList
open Experiment.Steel.Repr.M

#push-options "--ifuel 1"

/// We define a "monad" (which does not satisfy the monad laws) on [M.repr]. 

(****** Call *)

#push-options "--z3rlimit 20"
inline_for_extraction noextract
let repr_of_steel_steel
      (a : Type) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
      (tcs : tree_cond_Spec a pre post)
      ($f : repr_steel_t SH.KSteel a pre post req ens)
  : (let c = TCspec #a #pre #post #req #ens tcs in
     repr_steel_t SH.KSteel a tcs.tcs_pre tcs.tcs_post (tree_req _ c) (tree_ens _ c))
  = SH.steel_f (fun () ->
    (**) tcs.tcs_pre_eq.veq_g _;
    (**) steel_elim_vprop_of_list_append_f pre tcs.tcs_frame;
    let (x : a) = SH.steel_u f () in
    (**) steel_intro_vprop_of_list_append_f (post x) tcs.tcs_frame;
    (**) (tcs.tcs_post_eq x).veq_g _;
    Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let repr_of_steel_ghost_steel
      (a : Type) (opened : Mem.inames) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
      (tcs : tree_cond_Spec a pre post)
      ($f : repr_steel_t (SH.KGhost opened) a pre post req ens)
  : (let c = TCspec #a #pre #post #req #ens tcs in
     repr_steel_t (SH.KGhost opened) a tcs.tcs_pre tcs.tcs_post (tree_req _ c) (tree_ens _ c))
  = SH.ghost_f #opened (fun () ->
    (**) tcs.tcs_pre_eq.veq_g _;
    (**) steel_elim_vprop_of_list_append_f pre tcs.tcs_frame;
    let (x : a) = SH.ghost_u f () in
    (**) steel_intro_vprop_of_list_append_f (post x) tcs.tcs_frame;
    (**) (tcs.tcs_post_eq x).veq_g _;
    (**) noop ();
    x)
#pop-options


[@@ __repr_M__]
let tree_of_steel_r
      (#ek : SH.effect_kind) (#a : Type)
      (#pre : pre_t) (#post : post_t a) (#req : req_t pre) (#ens : ens_t pre a post)
      ($f : repr_steel_t ek a pre post req ens)
  : prog_tree a
  = Tspec a pre post req ens

[@@ __repr_M__]
inline_for_extraction noextract
let repr_of_steel_r
      (#a : Type) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
      ($f : repr_steel_t SH.KSteel a pre post req ens)
  : repr SH.KSteel a
  = {
    repr_tree  = tree_of_steel_r f;
    repr_steel = (fun pre'0 post'0 c ->
                    let TCspec tcs = c in
                    repr_of_steel_steel a pre post req ens tcs f)
  }

[@@ __repr_M__]
inline_for_extraction noextract
let repr_of_steel_ghost_r
      (#a : Type) (#opened : Mem.inames) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
      ($f : repr_steel_t (SH.KGhost opened) a pre post req ens)
  : repr (SH.KGhost opened) a
  = {
    repr_tree  = tree_of_steel_r f;
    repr_steel = (fun pre'0 post'0 c ->
                    let TCspec tcs = c in
                    repr_of_steel_ghost_steel a opened pre post req ens tcs f)
  }


[@@ __repr_M__]
let tree_of_steel
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      ($f : SH.unit_steel a pre post req ens)
  : prog_tree a
  = TspecS a pre post req ens

[@@ __repr_M__]
inline_for_extraction noextract
let repr_of_steel
      (#a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      ($f : SH.unit_steel a pre post req ens)
  : repr SH.KSteel a
  = {
    repr_tree  = tree_of_steel f;
    repr_steel = (fun pre'0 post'0 c ->
                    let TCspecS tr tcs = c in
                    repr_of_steel_steel a tr.r_pre tr.r_post tr.r_req tr.r_ens
                                        tcs (repr_steel_of_steel tr f))
  }

[@@ __repr_M__]
inline_for_extraction noextract
let repr_of_steel_ghost
      (#a : Type) (#opened : Mem.inames)
      (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      ($f : SH.unit_steel_ghost a opened pre post req ens)
  : repr (SH.KGhost opened) a
  = {
    repr_tree  = TspecS a pre post req ens;
    repr_steel = (fun pre'0 post'0 c ->
                    let TCspecS tr tcs = c in
                    repr_of_steel_ghost_steel a opened tr.r_pre tr.r_post tr.r_req tr.r_ens
                                        tcs (repr_steel_of_steel_ghost tr f))
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
let return (#a : Type) (x : a) : repr SH.KSteel a
  = return_hint x (fun _ -> [])

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
let return_ghost (#a : Type) (#opened : Mem.inames) (x : a) : repr (SH.KGhost opened) a
  = return_ghost_hint x (fun _ -> [])


(****** Bind *)

let elim_tree_req_bind (#a #b : Type) (f : prog_tree a) (g : a -> prog_tree b)
      (#pre : pre_t) (#post : post_t b) (#itm : post_t a)
      (cf  : tree_cond f pre itm) (cg : (x:a) -> tree_cond (g x) (itm x) post)
      (sl0 : t_of (vprop_of_list pre))
  : Lemma (requires tree_req _ (TCbind #a #b #f #g pre itm post cf cg) (vpl_sels_f pre sl0))
          (ensures  tree_req f cf (vpl_sels_f pre sl0) /\
                    (forall (x : a) (sl1 : t_of (vprop_of_list (itm x))) .
                      tree_ens f cf (vpl_sels_f pre sl0) x (vpl_sels_f (itm x) sl1) ==>
                      tree_req (g x) (cg x) (vpl_sels_f (itm x) sl1)))
  = assert_norm (tree_req _ (TCbind #a #b #f #g pre itm post cf cg) (vpl_sels_f pre sl0) == (
      tree_req f cf (vpl_sels_f pre sl0) /\
      (forall (x : a) (sl1 : sl_f (itm x)) .
         tree_ens f cf (vpl_sels_f pre sl0) x sl1 ==> tree_req (g x) (cg x) sl1)
    ))

let intro_tree_ens_bind (#a #b : Type) (f : prog_tree a) (g : a -> prog_tree b)
      (#pre : pre_t) (#post : post_t b) (#itm : post_t a)
      (cf  : tree_cond f pre itm) (cg : (x:a) -> tree_cond (g x) (itm x) post)
      (sl0 : t_of (vprop_of_list pre)) (x : a) (sl1 : t_of (vprop_of_list (itm x)))
      (y : b) (sl2 : t_of (vprop_of_list (post y)))
  : Lemma (requires tree_req f cf (vpl_sels_f pre sl0) /\
                    tree_ens f cf (vpl_sels_f pre sl0) x (vpl_sels_f (itm x) sl1) /\
                    tree_ens (g x) (cg x) (vpl_sels_f (itm x) sl1) y (vpl_sels_f (post y) sl2))
          (ensures  tree_ens _ (TCbind #a #b #f #g pre itm post cf cg)
                             (vpl_sels_f pre sl0) y (vpl_sels_f (post y) sl2))
  = assert_norm (tree_ens _ (TCbind #a #b #f #g pre itm post cf cg)
                          (vpl_sels_f pre sl0) y (vpl_sels_f (post y) sl2) == (
        (exists (x : a) (sl1 : sl_f (itm x)) .
          tree_ens f cf (vpl_sels_f pre sl0) x sl1 /\
          tree_ens (g x) (cg x) sl1 y (vpl_sels_f (post y) sl2))
    ))


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
    (**) elim_tree_req_bind f g cf cg sl0;
    let x = SH.steel_u rf () in
    (**) let sl1 = gget (vprop_of_list (itm x)) in
    let y = SH.steel_u (rg x) () in
    (**) let sl2 = gget (vprop_of_list (post y)) in
    (**) intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2;
    Steel.Effect.Atomic.return y)

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
    (**) elim_tree_req_bind f g cf cg sl0;
    let x = SH.ghost_u rf () in
    (**) let sl1 = gget (vprop_of_list (itm x)) in
    let y = SH.ghost_u (rg x) () in
    (**) let sl2 = gget (vprop_of_list (post y)) in
    (**) intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2;
    (**) noop ();
    y)


[@@ __repr_M__]
inline_for_extraction noextract
let bind (#a #b : Type) (f : repr SH.KSteel a) (g : a -> repr SH.KSteel b)
  : repr SH.KSteel b
  = {
    repr_tree  = Tbind a b f.repr_tree (fun x -> (g x).repr_tree);
    repr_steel = (fun pre0 post0 c ->
                    let (TCbind #a' #b' #tf #tg pre itm post cf cg) = c in
                    let rg (x : a) : repr_steel_t SH.KSteel b (itm x) post _ _
                                   = (g x).repr_steel _ _ (cg x) in
                    bind_steel a b tf tg pre itm post cf cg (f.repr_steel _ _ cf) rg)
  }

[@@ __repr_M__]
inline_for_extraction noextract
let bind_ghost (#a #b : Type) (#opened : Mem.inames)
               (f : repr (SH.KGhost opened) a) (g : a -> repr (SH.KGhost opened) b)
  : repr (SH.KGhost opened) b
  = {
    repr_tree  = Tbind a b f.repr_tree (fun x -> (g x).repr_tree);
    repr_steel = (fun pre0 post0 c ->
                    let (TCbind #a' #b' #tf #tg pre itm post cf cg) = c in
                    let rg (x : a) : repr_steel_t (SH.KGhost opened) b (itm x) post _ _
                                   = (g x).repr_steel _ _ (cg x) in
                    bind_ghost_steel a b opened tf tg pre itm post cf cg (f.repr_steel _ _ cf) rg)
  }



(****** Bind pure *)

inline_for_extraction noextract
let bindP_steel
      (a : Type) (b : Type) (wp : pure_wp a) ($f : unit -> PURE a wp) (g : (a -> prog_tree b))
      (pre : pre_t) (post : post_t b)
      (cg : ((x : a) -> tree_cond (g x) pre post))
      ($rg : (x : a) -> repr_steel_t SH.KSteel b pre post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbindP #a #b #wp #g pre post cg in
     repr_steel_t SH.KSteel b pre post (tree_req _ c) (tree_ens _ c))
  = 
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    SH.steel_f (fun () ->
    let x = f () in
    SH.steel_u (rg x) ())

inline_for_extraction noextract
let bindP_ghost_steel
      (a : Type) (b : Type) (opened : Mem.inames) (wp : pure_wp a) ($f : unit -> GHOST a wp) (g : (a -> prog_tree b))
      (pre : pre_t) (post : post_t b)
      (cg : ((x : a) -> tree_cond (g x) pre post))
      ($rg : (x : a) -> repr_steel_t (SH.KGhost opened) b pre post (tree_req (g x) (cg x)) (tree_ens (g x) (cg x)))
  : (let c = TCbindP #a #b #wp #g pre post cg in
     repr_steel_t (SH.KGhost opened) b pre post (tree_req _ c) (tree_ens _ c))
  =
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    SH.ghost_f #opened (fun () ->
    let x = f () in
    SH.ghost_u (rg x) ())

[@@ __repr_M__]
inline_for_extraction noextract
let bindP (#a #b : Type) (wp : pure_wp a) ($f : unit -> PURE a wp) (g : a -> repr SH.KSteel b)
  : repr SH.KSteel b
  = {
    repr_tree  = TbindP a b wp (fun x -> (g x).repr_tree);
    repr_steel = (fun pre0 post0 c ->
                    let (TCbindP #a' #b' #wp #tg pre post cg) = c in
                    let rg (x : a) : repr_steel_t SH.KSteel b pre post _ _
                                   = (g x).repr_steel _ _ (cg x) in
                    bindP_steel a b wp f tg pre post cg rg)
  }

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
                    let (TCif pre post cthn cels) = c in
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


(****** SteelGhost to Steel *)

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


inline_for_extraction noextract
let ghost_to_steel_steel_ct_aux (a : Type) (t : prog_tree a) (pre : pre_t) (post : post_t a)
      (c : tree_cond t pre post)
      ($r : repr_steel_t (SH.KGhost Set.empty) a pre post (tree_req t c) (tree_ens t c))
  : SteelGhost (Ghost.erased a) Set.empty
             (vprop_of_list pre) (fun x -> vprop_of_list (post (Ghost.reveal x)))
             (fun h0 -> tree_req t c (sel pre h0))
             (fun h0 x h1 -> tree_ens t c (sel pre h0) (Ghost.reveal x) (sel (post (Ghost.reveal x)) h1))
  = let x = SH.ghost_u r () in Ghost.hide x

inline_for_extraction noextract
let ghost_to_steel_steel_ct (a : Type) (t : prog_tree a) (pre : pre_t) (post : post_t a)
      (c : tree_cond t pre post)
      ($r : repr_steel_t (SH.KGhost Set.empty) a pre post (tree_req t c) (tree_ens t c))
      (rv : (x : Ghost.erased a) -> (x' : a { x' == Ghost.reveal x }))
  : repr_steel_t SH.KSteel a pre post (tree_req t c) (tree_ens t c)
  = SH.steel_f (fun () ->
    let x : Ghost.erased a = ghost_to_steel_steel_ct_aux a t pre post c r in
    let x' : a = rv x in
    change_equal_slprop (vprop_of_list (post (Ghost.reveal x))) (vprop_of_list (post x'));
    Steel.Effect.Atomic.return x'
  )

// TODO: SteelAtomic
