module Experiment.Steel.Combinators

module U   = Learn.Util
module G   = FStar.Ghost
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

#set-options "--ifuel 1 --ide_id_info_off"

/// We define a "monad" (which does not satisfy the monad laws) on [M.repr]. 

unfold
let repr_steel_tc
      (ek : SH.effect_kind) (#a : Type) (#t : prog_tree a) (#pre : pre_t) (#post : post_t a)
      ($tc : tree_cond t pre post)
  : Type
  = repr_steel_t ek a pre post (tree_req t tc) (tree_ens t tc)

(****** Call *)

inline_for_extraction noextract
val tcspec_steel
      (a : Type) (ek : SH.effect_kind)
      (pre : G.erased pre_t) (post : G.erased (post_t a)) (ro : G.erased vprop_list)
      (req : sl_f pre -> sl_f ro -> Type0) (ens : sl_f pre -> (x : a) -> sl_f (G.reveal post x) -> sl_f ro -> Type0)
      (tcs : G.erased (tree_cond_Spec a L.(pre @ ro) (spc_post1 (Mkspec_r pre post ro req ens))))
      ($f : spc_steel_t ek (Mkspec_r pre post ro req ens))
  : repr_steel_tc ek (TCspec #a #(spec_r_exact (Mkspec_r pre post ro req ens)) _ SpecExact tcs)

[@@ __repr_M__]
let tree_of_steel_r (#ek : SH.effect_kind) (#a : Type) (#s : spec_r a) ($f : spc_steel_t ek s)
  : prog_tree a
  = Tspec a (spec_r_exact s)

[@@ __repr_M__]
inline_for_extraction noextract
let repr_of_steel_r
      (#a : Type) (s : spec_r a) (#ek : SH.effect_kind) ($f : spc_steel_t ek s)
  : repr ek a
  = {
    repr_tree  = tree_of_steel_r f;
    repr_steel = (fun pre'0 post'0 c ->
                    let TCspec _ _ tcs = c in
                    let Mkspec_r pre0 post0 ro0 req0 ens0 = s in
                    tcspec_steel a ek pre0 post0 ro0 req0 ens0 tcs f)
  }


[@@ __repr_M__]
let tree_of_steel
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (#ek : SH.effect_kind) ($f : SH.steel a pre post req ens ek)
  : prog_tree a
  = Tspec a (spec_r_steel pre post req ens)

[@@ __repr_M__]
inline_for_extraction noextract
let repr_of_steel
      (#a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      (#ek : SH.effect_kind) ($f : SH.steel a pre post req ens ek)
  : repr ek a
  = {
    repr_tree  = tree_of_steel f;
    repr_steel = (fun pre'0 post'0 c ->
                    let TCspec #a #sp s sh tcs = c in
                    let SpecSteel tr (Mkspec_find_ro (Mkspec_r pre0 post0 ro0 req0 ens0)
                                                     pre_eq post_eq req_eq ens_eq)
                      = U.cast (spec_r_steel pre post req ens s) sh in
                    let sr = Mkspec_find_ro (Mkspec_r pre0 post0 ro0 req0 ens0)
                                            pre_eq post_eq req_eq ens_eq in
                    tcspec_steel a ek pre0 post0 ro0 req0 ens0 tcs
                       (spec_r_of_find_ro #a #tr.r_pre #tr.r_post #tr.r_req #tr.r_ens sr (repr_of_steel tr f)))
  }


(****** Return *)

inline_for_extraction noextract
val return_steel
      (a : Type) (ek : SH.effect_kind) (x : a) (sl_hint : option (post_t a))
      (pre : G.erased pre_t) (post : G.erased (post_t a))
      (e : Veq.vequiv pre (G.reveal post x))
  : repr_steel_tc ek (TCret #a #x #sl_hint pre post e)

[@@ __repr_M__]
inline_for_extraction noextract
let return_hint (ek : SH.effect_kind) (#a : Type) (x : a) (sl_hint : option (post_t a))
  : repr ek a
  = {
    repr_tree  = Tret a x sl_hint;
    repr_steel = (fun pre0 post0 c ->
        let TCret pre post p = c in
        return_steel a ek x sl_hint pre post p)
  }

[@@ __repr_M__]
inline_for_extraction noextract
let return (ek : SH.effect_kind) (#a : Type) (x : a) : repr ek a
  = return_hint ek x None


(****** Bind *)

type bind_steel_t (ek0 ek1 ek2 : SH.effect_kind) =
      (a : Type) ->  (b : Type) -> (f : G.erased (prog_tree a)) -> (g : G.erased (a -> prog_tree b)) ->
      (pre : G.erased pre_t) -> (itm : G.erased (post_t a)) -> (post : G.erased (post_t b)) ->
      (cf : G.erased (tree_cond f pre itm)) ->
      (cg : G.erased ((x : a) -> tree_cond (G.reveal g x) (G.reveal itm x) post)) ->
      (rf : repr_steel_tc ek0 cf) ->
      (rg : ((x : a) -> repr_steel_tc ek1 (G.reveal cg x))) ->
      repr_steel_tc ek2 (TCbind #a #b #f #g pre itm post cf cg)

inline_for_extraction noextract
val bind_steel__steel
  : bind_steel_t SH.KSteel SH.KSteel SH.KSteel

inline_for_extraction noextract
val bind_steel__atomic_ghost (o : Mem.inames)
  : bind_steel_t (SH.KAtomic o) (SH.KGhostI o) (SH.KAtomic o)

inline_for_extraction noextract
val bind_steel__ghost_atomic (o : Mem.inames)
  : bind_steel_t (SH.KGhostI o) (SH.KAtomic o) (SH.KAtomic o)

inline_for_extraction noextract
val bind_steel__ghostI (o : Mem.inames)
  : bind_steel_t (SH.KGhostI o) (SH.KGhostI o) (SH.KGhostI o)

inline_for_extraction noextract
val bind_steel__ghost(o : Mem.inames)
  : bind_steel_t (SH.KGhost o) (SH.KGhost o) (SH.KGhost o)

(**) private val end_bind_steel : unit

[@@ __repr_M__]
inline_for_extraction noextract
let bind_ek (#a #b : Type) (ek0 ek1 ek2 : SH.effect_kind) (s : bind_steel_t ek0 ek1 ek2)
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
  = bind_ek SH.KSteel SH.KSteel SH.KSteel bind_steel__steel f g

[@@ __repr_M__]
inline_for_extraction noextract
let bind_ghost (#a #b : Type) (#opened : Mem.inames)
               (f : repr (SH.KGhost opened) a) (g : a -> repr (SH.KGhost opened) b)
  : repr (SH.KGhost opened) b
  = bind_ek (SH.KGhost opened) (SH.KGhost opened) (SH.KGhost opened) (bind_steel__ghost opened) f g


(****** Bind pure *)

inline_for_extraction noextract
val bindP_steel__ghost
      (a : Type) (b : Type) (opened : Mem.inames) (wp : pure_wp a) ($f : unit -> GHOST a wp)
      (g : G.erased (a -> prog_tree b))
      (pre : G.erased pre_t) (post : G.erased (post_t b))
      (cg : G.erased ((x : a) -> tree_cond (G.reveal g x) pre post))
      (rg : (x : a) -> repr_steel_tc (SH.KGhost opened) (G.reveal cg x))
  : repr_steel_tc (SH.KGhost opened) (TCbindP #a #b #wp #g pre post cg)

inline_for_extraction noextract
val bindP_steel
      (a : Type) (b : Type) (ek : SH.effect_kind) (wp : pure_wp a) ($f : unit -> PURE a wp)
      (g : G.erased (a -> prog_tree b))
      (pre : G.erased pre_t) (post : G.erased (post_t b))
      (cg : ((x : a) -> tree_cond (G.reveal g x) pre post))
      (rg : (x : a) -> repr_steel_tc ek (G.reveal cg x))
  : repr_steel_tc ek (TCbindP #a #b #wp #g pre post cg)

#push-options "--ifuel 1 --fuel 1 --z3rlimit 10"
[@@ __repr_M__]
inline_for_extraction noextract
let bindP (#a #b : Type) (ek : SH.effect_kind) (wp : pure_wp a) ($f : unit -> PURE a wp) (g : a -> repr ek b)
  : repr ek b
  = {
    repr_tree  = TbindP a b wp (fun x -> (g x).repr_tree);
    repr_steel = (fun pre0 post0 c ->
                    let (TCbindP #a' #b' #wp #tg pre post cg) = c in
                    let rg (x : a) : repr_steel_t ek b pre post _ _
                                   = (g x).repr_steel _ _ (cg x) in
                    bindP_steel a b ek wp f tg pre post cg rg)
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
                    bindP_steel__ghost a b opened wp f tg pre post cg rg)
  }
#pop-options


(****** If-then-else *)

inline_for_extraction noextract
val ite_steel
      (a : Type) (guard : bool)
      (thn  : G.erased (prog_tree a)) (els : G.erased (prog_tree a))
      (pre  : G.erased pre_t) (post : G.erased (post_t a))
      (cthn : G.erased (tree_cond thn pre post))
      (cels : G.erased (tree_cond els pre post))
      (rthn : repr_steel_tc SH.KSteel cthn)
      (rels : repr_steel_tc SH.KSteel cels)
  : repr_steel_tc SH.KSteel (TCif #a #guard #thn #els pre post cthn cels)

inline_for_extraction noextract
val ite_ghost_steel
      (a : Type) (opened : Mem.inames) (guard : bool)
      (thn  : G.erased (prog_tree a)) (els : G.erased (prog_tree a))
      (pre  : G.erased pre_t) (post : G.erased (post_t a))
      (cthn : G.erased (tree_cond thn pre post))
      (cels : G.erased (tree_cond els pre post))
      (rthn : repr_steel_tc (SH.KGhost opened) cthn)
      (rels : repr_steel_tc (SH.KGhost opened) cels)
  : repr_steel_tc (SH.KGhost opened) (TCif #a #guard #thn #els pre post cthn cels)


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

[@@ __extraction__]
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

let repr_steel_lift_t (a : Type) (ek0 ek1 : SH.effect_kind) =
  (pre : G.erased pre_t) -> (post : G.erased (post_t a)) ->
  (req : req_t pre) -> (ens : ens_t pre a post) ->
  (f : repr_steel_t ek0 a pre post req ens) ->
  repr_steel_t ek1 a pre post req ens
    
inline_for_extraction noextract
val repr_steel_lift_ghost_ghostI (a : Type) (opened : Mem.inames) (e : erasable_t a)
  : repr_steel_lift_t a (SH.KGhost opened) (SH.KGhostI opened)

inline_for_extraction noextract
val repr_steel_lift_ghostI_atomic (a : Type) (opened : Mem.inames)
  : repr_steel_lift_t a (SH.KGhostI opened) (SH.KAtomic opened)

inline_for_extraction noextract
val repr_steel_lift_atomic_steel (a : Type)
  : repr_steel_lift_t a (SH.KAtomic Set.empty) SH.KSteel

[@@ __extraction__]
inline_for_extraction noextract
let repr_steel_lift1
      (#a : Type) (#pre : pre_t) (#post : post_t a) (#req : req_t pre) (#ens : ens_t pre a post)
      (#ek0 #ek1 : SH.effect_kind) (l : steel_liftable1 a ek0 ek1)
      (f : repr_steel_t ek0 a pre post req ens)
  : repr_steel_t ek1 a pre post req ens
  = match l with
  | Lift_ghost_ghostI e o -> repr_steel_lift_ghost_ghostI  a o e pre post req ens f
  | Lift_ghostI_atomic  o -> repr_steel_lift_ghostI_atomic a o   pre post req ens f
  | Lift_atomic_steel     -> repr_steel_lift_atomic_steel  a     pre post req ens f

[@@ __extraction__]
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
val ghost_to_steel_steel (a : Type)
      (t : G.erased (prog_tree (Ghost.erased a)))
      (pre : G.erased pre_t) (post : G.erased (post_t (Ghost.erased a)))
      (c : G.erased (tree_cond t pre post))
      ($r : repr_steel_tc (SH.KGhost Set.empty) c)
  : repr_steel_t SH.KSteel (Ghost.erased a) pre post (tree_req t c) (tree_ens t c)

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
