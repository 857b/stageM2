module Experiment.Steel.Combinators

module L   = FStar.List.Pure

#set-options "--ifuel 1 --ide_id_info_off"

(****** Call *)

#push-options "--z3rlimit 30"
inline_for_extraction noextract
let tcspec_steel__steel
      (a : Type)
      (pre : G.erased pre_t) (post : G.erased (post_t a)) (ro : G.erased vprop_list)
      (req : sl_f pre -> sl_f ro -> Type0) (ens : sl_f pre -> (x : a) -> sl_f (G.reveal post x) -> sl_f ro -> Type0)
      (tcs : G.erased (tree_cond_Spec a L.(pre @ ro) (spc_post1 (Mkspec_r pre post ro req ens))))
      ($f : spc_steel_t SH.KSteel (Mkspec_r pre post ro req ens))
  : repr_steel_tc SH.KSteel (TCspec #a #(spec_r_exact (Mkspec_r pre post ro req ens)) _ SpecExact tcs)
  = SH.steel_f (fun () ->
    (**) tcs.tcs_pre_eq.veq_g _;
    (**) elim_vpl_append L.(pre @ ro) tcs.tcs_frame;
    (**) elim_vpl_append pre ro;
    let (x : a) = SH.steel_c f () in
    (**) intro_vpl_append (G.reveal post x) ro;
    (**) intro_vpl_append L.(G.reveal post x @ ro) tcs.tcs_frame;
    (**) (tcs.tcs_post_eq x).veq_g _;
    Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let tcspec_steel__atomic
      (a : Type) (opened : Mem.inames)
      (pre : G.erased pre_t) (post : G.erased (post_t a)) (ro : G.erased vprop_list)
      (req : sl_f pre -> sl_f ro -> Type0) (ens : sl_f pre -> (x : a) -> sl_f (G.reveal post x) -> sl_f ro -> Type0)
      (tcs : G.erased (tree_cond_Spec a L.(pre @ ro) (spc_post1 (Mkspec_r pre post ro req ens))))
      ($f : spc_steel_t (SH.KAtomic opened) (Mkspec_r pre post ro req ens))
  : repr_steel_tc (SH.KAtomic opened) (TCspec #a #(spec_r_exact (Mkspec_r pre post ro req ens)) _ SpecExact tcs)
  = SH.atomic_f #opened (fun () ->
    (**) tcs.tcs_pre_eq.veq_g _;
    (**) elim_vpl_append L.(pre @ ro) tcs.tcs_frame;
    (**) elim_vpl_append pre ro;
    let (x : a) = SH.atomic_c f () in
    (**) intro_vpl_append (G.reveal post x) ro;
    (**) intro_vpl_append L.(G.reveal post x @ ro) tcs.tcs_frame;
    (**) (tcs.tcs_post_eq x).veq_g _;
    Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let tcspec_steel__ghostI
      (a : Type) (opened : Mem.inames)
      (pre : G.erased pre_t) (post : G.erased (post_t a)) (ro : G.erased vprop_list)
      (req : sl_f pre -> sl_f ro -> Type0) (ens : sl_f pre -> (x : a) -> sl_f (G.reveal post x) -> sl_f ro -> Type0)
      (tcs : G.erased (tree_cond_Spec a L.(pre @ ro) (spc_post1 (Mkspec_r pre post ro req ens))))
      ($f : spc_steel_t (SH.KGhostI opened) (Mkspec_r pre post ro req ens))
  : repr_steel_tc (SH.KGhostI opened) (TCspec #a #(spec_r_exact (Mkspec_r pre post ro req ens)) _ SpecExact tcs)
  = SH.ghostI_f #opened (fun () ->
    (**) tcs.tcs_pre_eq.veq_g _;
    (**) elim_vpl_append L.(pre @ ro) tcs.tcs_frame;
    (**) elim_vpl_append pre ro;
    let (x : a) = SH.ghostI_c f () in
    (**) intro_vpl_append (G.reveal post x) ro;
    (**) intro_vpl_append L.(G.reveal post x @ ro) tcs.tcs_frame;
    (**) (tcs.tcs_post_eq x).veq_g _;
    Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let tcspec_steel__ghost
      (a : Type) (opened : Mem.inames)
      (pre : G.erased pre_t) (post : G.erased (post_t a)) (ro : G.erased vprop_list)
      (req : sl_f pre -> sl_f ro -> Type0) (ens : sl_f pre -> (x : a) -> sl_f (G.reveal post x) -> sl_f ro -> Type0)
      (tcs : G.erased (tree_cond_Spec a L.(pre @ ro) (spc_post1 (Mkspec_r pre post ro req ens))))
      ($f : spc_steel_t (SH.KGhost opened) (Mkspec_r pre post ro req ens))
  : repr_steel_tc (SH.KGhost opened) (TCspec #a #(spec_r_exact (Mkspec_r pre post ro req ens)) _ SpecExact tcs)
  = SH.ghost_f #opened (fun () ->
    (**) tcs.tcs_pre_eq.veq_g _;
    (**) elim_vpl_append L.(pre @ ro) tcs.tcs_frame;
    (**) elim_vpl_append pre ro;
    let (x : a) = SH.ghost_c f () in
    (**) intro_vpl_append (G.reveal post x) ro;
    (**) intro_vpl_append L.(G.reveal post x @ ro) tcs.tcs_frame;
    (**) (tcs.tcs_post_eq x).veq_g _;
    (**) noop ();
    x)
#pop-options

inline_for_extraction noextract
let tcspec_steel
      (a : Type) (ek : SH.effect_kind)
      (pre : G.erased pre_t) (post : G.erased (post_t a)) (ro : G.erased vprop_list)
      (req : sl_f pre -> sl_f ro -> Type0) (ens : sl_f pre -> (x : a) -> sl_f (G.reveal post x) -> sl_f ro -> Type0)
      (tcs : G.erased (tree_cond_Spec a L.(pre @ ro) (spc_post1 (Mkspec_r pre post ro req ens))))
      ($f : spc_steel_t ek (Mkspec_r pre post ro req ens))
  : repr_steel_tc ek (TCspec #a #(spec_r_exact (Mkspec_r pre post ro req ens)) _ SpecExact tcs)
  = match ek with
  | SH.KSteel    -> tcspec_steel__steel  a   pre post ro req ens tcs f
  | SH.KAtomic o -> tcspec_steel__atomic a o pre post ro req ens tcs f
  | SH.KGhostI o -> tcspec_steel__ghostI a o pre post ro req ens tcs f
  | SH.KGhost  o -> tcspec_steel__ghost  a o pre post ro req ens tcs f

(****** Return *)

inline_for_extraction noextract
let return_steel__steel
      (a : Type) (x : a) (sl_hint : option (post_t a))
      (pre : G.erased pre_t) (post : G.erased (post_t a))
      (e : Veq.vequiv pre (G.reveal post x))
  : repr_steel_tc SH.KSteel (TCret #a #x #sl_hint pre post e)
  = SH.steel_f (fun () ->
    (**) e.veq_g _;
    Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let return_steel__atomic
      (a : Type) (opened : Mem.inames) (x : a) (sl_hint : option (post_t a))
      (pre : G.erased pre_t) (post : G.erased (post_t a))
      (e : Veq.vequiv pre (G.reveal post x))
  : repr_steel_tc (SH.KAtomic opened) (TCret #a #x #sl_hint pre post e)
  = SH.atomic_f #opened (fun () ->
    (**) e.veq_g _;
    Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let return_steel__ghostI
      (a : Type) (opened : Mem.inames) (x : a) (sl_hint : option (post_t a))
      (pre : G.erased pre_t) (post : G.erased (post_t a))
      (e : Veq.vequiv pre (G.reveal post x))
  : repr_steel_tc (SH.KGhostI opened) (TCret #a #x #sl_hint pre post e)
  = SH.ghostI_f #opened (fun () ->
    (**) e.veq_g _;
    Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let return_steel__ghost
      (a : Type) (opened : Mem.inames) (x : a) (sl_hint : option (post_t a))
      (pre : G.erased pre_t) (post : G.erased (post_t a))
      (e : Veq.vequiv pre (G.reveal post x))
  : repr_steel_tc (SH.KGhost opened) (TCret #a #x #sl_hint pre post e)
  = SH.ghost_f #opened (fun () ->
    (**) e.veq_g _;
    x)

inline_for_extraction noextract
let return_steel
      (a : Type) (ek : SH.effect_kind) (x : a) (sl_hint : option (post_t a))
      (pre : G.erased pre_t) (post : G.erased (post_t a))
      (e : Veq.vequiv pre (G.reveal post x))
  : repr_steel_tc ek (TCret #a #x #sl_hint pre post e)
  = match ek with
  | SH.KSteel    -> return_steel__steel  a   x sl_hint pre post e
  | SH.KAtomic o -> return_steel__atomic a o x sl_hint pre post e
  | SH.KGhostI o -> return_steel__ghostI a o x sl_hint pre post e
  | SH.KGhost  o -> return_steel__ghost  a o x sl_hint pre post e

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

#push-options "--ifuel 0 --fuel 0 --z3rlimit 20"
inline_for_extraction noextract
let bind_steel__steel a b f g pre itm post cf cg rf rg
  = SH.steel_f (fun () ->
    (**) let sl0 = gget (vprop_of_list pre) in
    (**) (elim_tree_req_bind f g cf cg sl0; ());
    let x = SH.steel_u rf () in
    (**) let sl1 = gget (vprop_of_list (G.reveal itm x)) in
    let y = SH.steel_u (rg x) () in
    (**) let sl2 = gget (vprop_of_list (G.reveal post y)) in
    (**) (intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2; ());
    Steel.Effect.Atomic.return y)

inline_for_extraction noextract
let bind_steel__atomic_ghost o a b f g pre itm post cf cg rf rg
  = SH.atomic_f (fun () ->
    (**) let sl0 = gget (vprop_of_list pre) in
    (**) (elim_tree_req_bind f g cf cg sl0; ());
    let x = SH.atomic_u rf () in
    (**) let sl1 = gget (vprop_of_list (G.reveal itm x)) in
    let y = SH.ghostI_u (rg x) () in
    (**) let sl2 = gget (vprop_of_list (G.reveal post y)) in
    (**) (intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2; ());
    Steel.Effect.Atomic.return y)

inline_for_extraction noextract
let bind_steel__ghost_atomic o a b f g pre itm post cf cg rf rg
  = SH.atomic_f (fun () ->
    (**) let sl0 = gget (vprop_of_list pre) in
    (**) (elim_tree_req_bind f g cf cg sl0; ());
    let x = SH.ghostI_u rf () in
    (**) let sl1 = gget (vprop_of_list (G.reveal itm x)) in
    let y = SH.atomic_u (rg x) () in
    (**) let sl2 = gget (vprop_of_list (G.reveal post y)) in
    (**) (intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2; ());
    Steel.Effect.Atomic.return y)

inline_for_extraction noextract
let bind_steel__ghostI o a b f g pre itm post cf cg rf rg
  = SH.ghostI_f (fun () ->
    (**) let sl0 = gget (vprop_of_list pre) in
    (**) (elim_tree_req_bind f g cf cg sl0; ());
    let x = SH.ghostI_u rf () in
    (**) let sl1 = gget (vprop_of_list (G.reveal itm x)) in
    let y = SH.ghostI_u (rg x) () in
    (**) let sl2 = gget (vprop_of_list (G.reveal post y)) in
    (**) (intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2; ());
    Steel.Effect.Atomic.return y)

inline_for_extraction noextract
let bind_steel__ghost o a b f g pre itm post cf cg rf rg
  = SH.ghost_f (fun () ->
    (**) let sl0 = gget (vprop_of_list pre) in
    (**) (elim_tree_req_bind f g cf cg sl0; ());
    let x = SH.ghost_u rf () in
    (**) let sl1 = gget (vprop_of_list (G.reveal itm x)) in
    let y = SH.ghost_u (rg x) () in
    (**) let sl2 = gget (vprop_of_list (G.reveal post y)) in
    (**) (intro_tree_ens_bind f g cf cg sl0 x sl1 y sl2; ());
    (**) noop ();
    y)
#pop-options

(**) private let end_bind_steel = ()

(****** Bind pure *)

type bindP_steel_t (ek : SH.effect_kind) =
      (a : Type) -> (b : Type) -> (wp : pure_wp a) -> (f : unit -> PURE a wp) ->
      (g : G.erased (a -> prog_tree b)) ->
      (pre : G.erased pre_t) -> (post : G.erased (post_t b)) ->
      (cg : G.erased ((x : a) -> tree_cond (G.reveal g x) pre post)) ->
      (rg : ((x : a) -> repr_steel_tc ek (G.reveal cg x))) ->
      repr_steel_tc ek (TCbindP #a #b #wp #g pre post cg)

inline_for_extraction noextract
let bindP_steel__steel : bindP_steel_t SH.KSteel
  = fun a b wp f g pre post cg rg ->
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    SH.steel_f (fun () ->
    let x = f () in
    SH.steel_u (rg x) ())

inline_for_extraction noextract
let bindP_steel__atomic o : bindP_steel_t (SH.KAtomic o)
  = fun a b wp f g pre post cg rg ->
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    SH.atomic_f (fun () ->
    let x = f () in
    SH.atomic_u (rg x) ())

inline_for_extraction noextract
let bindP_steel__ghostI o : bindP_steel_t (SH.KGhostI o)
  = fun a b wp f g pre post cg rg ->
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    SH.ghostI_f (fun () ->
    let x = f () in
    SH.ghostI_u (rg x) ())

inline_for_extraction noextract
let bindP_steel__ghost0 o : bindP_steel_t (SH.KGhost o)
  = fun a b wp f g pre post cg rg ->
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    SH.ghost_f (fun () ->
    let x = f () in
    SH.ghost_u (rg x) ())

inline_for_extraction noextract
let bindP_steel__ghost a b o wp f g pre post cg rg
  =
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    SH.ghost_f (fun () ->
    let x = f () in
    SH.ghost_u (rg x) ())

inline_for_extraction noextract
let bindP_steel
      (a : Type) (b : Type) (ek : SH.effect_kind) (wp : pure_wp a) ($f : unit -> PURE a wp)
      (g : G.erased (a -> prog_tree b))
      (pre : G.erased pre_t) (post : G.erased (post_t b))
      (cg : ((x : a) -> tree_cond (G.reveal g x) pre post))
      (rg : (x : a) -> repr_steel_tc ek (G.reveal cg x))
  : repr_steel_tc ek (TCbindP #a #b #wp #g pre post cg)
  = match ek with
  | SH.KSteel    -> bindP_steel__steel    a b wp f g pre post cg rg
  | SH.KAtomic o -> bindP_steel__atomic o a b wp f g pre post cg rg
  | SH.KGhostI o -> bindP_steel__ghostI o a b wp f g pre post cg rg
  | SH.KGhost  o -> bindP_steel__ghost0 o a b wp f g pre post cg rg

(****** If-then-else *)

type ite_steel_t (ek : SH.effect_kind) =
      (a : Type) -> (guard : bool) ->
      (thn  : G.erased (prog_tree a)) -> (els : G.erased (prog_tree a)) ->
      (pre  : G.erased pre_t) -> (post : G.erased (post_t a)) ->
      (cthn : G.erased (tree_cond thn pre post)) -> 
      (cels : G.erased (tree_cond els pre post)) -> 
      (rthn : repr_steel_tc ek cthn) -> 
      (rels : repr_steel_tc ek cels) ->
      repr_steel_tc ek (TCif #a #guard #thn #els pre post cthn cels)

inline_for_extraction
let ite_steel__steel : ite_steel_t SH.KSteel
  = fun a guard thn els pre post cthn cels rthn rels ->
    SH.steel_f (fun () ->
    if guard then SH.steel_u rthn () else SH.steel_u rels ())

inline_for_extraction
let ite_steel__ghostI o : ite_steel_t (SH.KGhostI o)
  = fun a guard thn els pre post cthn cels rthn rels ->
    SH.ghostI_f (fun () ->
    if guard then SH.ghostI_u rthn () else SH.ghostI_u rels ())

inline_for_extraction
let ite_steel__ghost o : ite_steel_t (SH.KGhost o)
  = fun a guard thn els pre post cthn cels rthn rels ->
    SH.ghost_f (fun () ->
    if guard then SH.ghost_u rthn () else SH.ghost_u rels ())


inline_for_extraction noextract
let ite_steel a ek guard thn els pre post cthn cels rthn rels
  = match ek with
  | SH.KSteel    -> ite_steel__steel    a guard thn els pre post cthn cels rthn rels
  | SH.KGhostI o -> ite_steel__ghostI o a guard thn els pre post cthn cels rthn rels
  | SH.KGhost  o -> ite_steel__ghost  o a guard thn els pre post cthn cels rthn rels

(***** [steel_liftable] *)

let repr_steel_lift_ghost_ghostI_aux
      (#a : Type) (#pre : G.erased pre_t) (#post : G.erased (post_t a))
      #req #ens #opened (f : repr_steel_t (SH.KGhost opened) a pre post req ens)
  : SH.unit_steel_ghost (Ghost.erased a) opened
      (vprop_of_list pre) (fun x -> vprop_of_list (G.reveal post (Ghost.reveal x)))
      (fun h0 -> req (sel_f pre h0))
      (fun h0 x h1 -> ens (sel_f pre h0) (Ghost.reveal x) (sel_f (G.reveal post (Ghost.reveal x)) h1))
  =
    fun () ->
      let x = SH.ghost_u f () in
      Ghost.hide x

inline_for_extraction noextract
let repr_steel_lift_ghost_ghostI a opened e pre post req ens f
  =
    SH.ghostI_f (fun () ->
      let x : Ghost.erased a = repr_steel_lift_ghost_ghostI_aux f () in
      let x' : a = e.erasable_rv x in
      change_equal_slprop (vprop_of_list (G.reveal post (Ghost.reveal x))) (vprop_of_list (G.reveal post x'));
      Steel.Effect.Atomic.return x'
  )

inline_for_extraction noextract
let repr_steel_lift_ghostI_atomic a opened pre post req ens f
  = SH.atomic_f (fun () -> SH.ghostI_u f ())

inline_for_extraction noextract
let repr_steel_lift_atomic_steel a pre post req ens f
  = SH.steel_f (fun () -> SH.atomic_u f ())

(****** SteelGhost to Steel (Monad) *)

inline_for_extraction noextract
let ghost_to_steel_steel (a : Type)
      (t : G.erased (prog_tree (Ghost.erased a)))
      (pre : G.erased pre_t) (post : G.erased (post_t (Ghost.erased a)))
      (c : G.erased (tree_cond t pre post))
      ($r : repr_steel_t (SH.KGhost Set.empty) (Ghost.erased a) pre post (tree_req t c) (tree_ens t c))
  : repr_steel_t SH.KSteel (Ghost.erased a) pre post (tree_req t c) (tree_ens t c)
  = SH.steel_f (SH.ghost_u r)
