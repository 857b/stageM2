module Learn.Steel.Util

module G = FStar.Ghost
module Mem = Steel.Memory

open Steel.Memory
open Steel.Effect.Common
open Steel.Effect.Atomic
open Steel.Effect
open FStar.Classical.Sugar
open Steel.FractionalPermission
open Steel.Reference


let pts_to_ref_injective_and
      (#a:Type u#0) (r:ref a)
      (p:perm)   (v0 v1:a) (m:mem)
  : Lemma
    (requires interp (pts_to_sl r p v0) m /\ interp (pts_to_sl r p v1) m)
    (ensures  v0 == v1)
  = pts_to_witinv r p;
    Mem.elim_wi (pts_to_sl r p) v0 v1 m

let noop_p (#opened) (p : vprop)
  : SteelGhost unit opened p (fun () -> p) (fun _ -> True) (fun h0 () h1 -> frame_equalities p h0 h1)
  = noop ()

(* TODO: use? *)
let slabsurd (#a : Type) (#opened:inames) (#p : vprop) (#q : a -> vprop) ()
  : SteelGhost a opened p q (requires fun _ -> False) (ensures fun _ _ _ -> False)
  = let rt : a = () in
    change_equal_slprop p (q rt);
    rt

let rewrite_vprop #opened (#p #q : vprop) ($rw : squash (p == q))
  : SteelGhost unit opened p (fun _ -> q)
               (requires fun _ -> True)
               (ensures fun h0 () h1 -> h1 q == h0 p)
  = change_equal_slprop p q

let eq_sym (#a : Type) (#x #y : a) ($p : squash (x == y)) : squash (y == x) = ()


(* expansion of a vprop *)

let expanded_vprop (v : vprop) : v':vprop{t_of v' == t_of v}
  = VUnit ({
    hp  = hp_of v;
    t   = t_of v;
    sel = sel_of v
  })

let intro_expanded_vprop_lem (v : vprop) (m : Mem.mem)
  : Lemma (requires Mem.interp (hp_of v) m)
          (ensures  Mem.interp (hp_of (expanded_vprop v)) m /\
                    sel_of (expanded_vprop v) m === sel_of v m)
  = ()

let elim_expanded_vprop_lem (v : vprop) (m : Mem.mem)
  : Lemma (requires Mem.interp (hp_of (expanded_vprop v)) m)
          (ensures  Mem.interp (hp_of v) m /\
                    sel_of (expanded_vprop v) m === sel_of v m)
  = ()

let intro_expanded_vprop #opened (v : vprop)
  : SteelGhost unit opened
               v (fun () -> expanded_vprop v)
               (requires fun _ -> True) (ensures fun h0 _ h1 -> h1 (expanded_vprop v) == h0 v)
  = change_slprop_rel v (expanded_vprop v)
                      (fun sl0 sl1 -> sl1 == sl0)
                      (intro_expanded_vprop_lem v)

let elim_expanded_vprop #opened (v : vprop)
  : SteelGhost unit opened
               (expanded_vprop v) (fun () -> v)
               (requires fun _ -> True) (ensures fun h0 _ h1 -> h0 (expanded_vprop v) == h1 v)
  = change_slprop_rel (expanded_vprop v) v
                      (fun sl0 sl1 -> sl0 == sl1)
                      (elim_expanded_vprop_lem v)


(* [pure] with a selector that gives a squash of the proposition *)

val pure_sl  (p : prop) : Mem.slprop u#1
val pure_sel (p : prop) : selector (squash p) (pure_sl p)

[@@__steel_reduce__]
let pure' (p : prop) : vprop' = {
  hp  = pure_sl  p;
  t   = squash   p;
  sel = pure_sel p
}
unfold let pure (p : prop) : vprop = VUnit (pure' p)

val intro_pure_lem (p : prop) (m : mem)
  : Lemma (requires p) (ensures interp (hp_of (pure p)) m)

val elim_pure_lem (p : prop) (m : mem)
  : Lemma (requires Mem.interp (hp_of (pure p)) m) (ensures p)


(* [vopt] *)

let vopt_sel_t (b : bool) (v : vprop) : Type = x : option (t_of v) {Some? x <==> b}
val vopt_sl    (b : bool) (v : vprop) : Mem.slprop u#1
val vopt_sel   (b : bool) (v : vprop) : selector (vopt_sel_t b v) (vopt_sl b v)

[@@__steel_reduce__]
let vopt' ([@@@smt_fallback] b : bool) (v : vprop) : vprop' = {
  hp  = vopt_sl    b v;
  t   = vopt_sel_t b v;
  sel = vopt_sel   b v
}
unfold let vopt ([@@@smt_fallback] b : bool) (v : vprop) : vprop = VUnit (vopt' b v)

val vopt_intro_t (#opened:Mem.inames) (v : vprop)
  : SteelGhost unit opened
      v (fun () -> vopt true v)
      (requires fun _ -> True) (ensures fun h0 () h1 -> h1 (vopt true v) == Some (h0 v))

val vopt_intro_f (#opened:Mem.inames) (v : vprop)
  : SteelGhost unit opened
      emp (fun () -> vopt false v)
      (requires fun _ -> True) (ensures fun h0 () h1 -> h1 (vopt false v) == None)

val vopt_elim_t (#opened:Mem.inames) (v : vprop)
  : SteelGhost unit opened
      (vopt true v) (fun () -> v)
      (requires fun _ -> True) (ensures fun h0 () h1 -> h0 (vopt true v) == Some (h1 v))

val vopt_elim_f (#opened:Mem.inames) (v : vprop)
  : SteelGhost unit opened
      (vopt false v) (fun () -> emp)
      (requires fun _ -> True) (ensures fun h0 () h1 -> h0 (vopt false v) == None)


(* [vexists] *)
(* TODO? $args *)

let vexists_indep (#a : Type) (v : a -> vprop) (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
  : Tot prop
  = forall (x0 x1 : a) (m : mem) .
      interp (hp_of (v x0)) m /\ interp (hp_of (v x1)) m ==>
      f x0 (sel_of (v x0) m) == f x1 (sel_of (v x1) m)

let vexists_indepD (#a : Type) (v : a -> vprop) (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t) 
                   (x0 x1 : a) (m : mem)
  : Lemma (requires vexists_indep #a v #t f /\
                    interp (hp_of (v x0)) m /\ interp (hp_of (v x1)) m)
          (ensures  f x0 (sel_of (v x0) m) == f x1 (sel_of (v x1) m))
  = ()

let vexists_indepI (#a : Type) (v : a -> vprop) (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
  (prf : (x0 : a) -> (x1 : a) -> (m : mem) ->
         Lemma (requires interp (hp_of (v x0)) m /\ interp (hp_of (v x1)) m)
               (ensures  f x0 (sel_of (v x0) m) == f x1 (sel_of (v x1) m)))
  : Lemma (ensures vexists_indep #a v #t f)
  = 
    introduce forall (x0 x1 : a) (m : mem) . interp (hp_of (v x0)) m /\ interp (hp_of (v x1)) m ==>
                                        f x0 (sel_of (v x0) m) == f x1 (sel_of (v x1) m)
      with introduce _ ==> _
      with _ . prf x0 x1 m

let vexists_indepI_unique (#a : Type) (v : a -> vprop)
  (prf : (x0 : a) -> (x1 : a) -> (m : mem) ->
         Lemma (requires interp (hp_of (v x0)) m /\ interp (hp_of (v x1)) m)
               (ensures  x0 == x1))
  : Lemma (ensures forall (t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
                   . {:pattern (vexists_indep #a v #t f)}
                     vexists_indep #a v #t f)
  = introduce forall t f . vexists_indep #a v #t f
      with vexists_indepI #a v #t f prf


val vexists_sl (#a : Type) (v : a -> vprop)
  : slprop u#1

val vexists_sel (#a : Type) (v : a -> vprop) (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
  : Pure (selector t (vexists_sl #a v))
         (requires vexists_indep v f) (ensures fun _ -> True)

[@__steel_reduce__]
let vexists' (#a : Type) (v : a -> vprop) (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
  : Pure vprop' (requires vexists_indep v f) (ensures fun _ -> True)
  = {
    hp  = vexists_sl  v;
    t   = t;
    sel = vexists_sel v f
  }

[@__steel_reduce__]
let vexists (#a : Type) (v : a -> vprop) (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
  : Pure vprop (requires vexists_indep v f) (ensures fun _ -> True)
  = VUnit (vexists' v f)


val intro_vexists_lem (#a : Type) (x : a) (v : a -> vprop)
                      (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
                      (m : mem)
  : Lemma (requires vexists_indep v f /\
                    interp (hp_of (v x)) m)
          (ensures  interp (hp_of (vexists v f)) m /\
                    vexists_sel v f m == f x (sel_of (v x) m))
  
val intro_vexists (#a : Type) (#opened:Mem.inames) (x : a) (v : a -> vprop)
                  (#t : Type) (f : ((x:a) -> normal (t_of (v x)) -> GTot t) {vexists_indep v f})
  : SteelGhost  unit opened
               (v x)      (fun () -> vexists v f)
               (fun _ -> True) (fun h0 () h1 -> h1 (vexists v f) == f x (h0 (v x)))

val witness_vexists_lem (#a : Type) (v : a -> vprop)
                        (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
                        (m : mem)
  : Ghost  a
          (requires vexists_indep v f /\
                    interp (hp_of (vexists v f)) m)
          (ensures fun x ->
                    interp (hp_of (v x)) m /\
                    vexists_sel v f m == f x (sel_of (v x) m))

val witness_vexists (#a : Type) (#opened:Mem.inames) (v : a -> vprop)
                    (#t : Type) (f : ((x:a) -> normal (t_of (v x)) -> GTot t) {vexists_indep v f})
  : SteelGhost (G.erased a) opened
               (vexists v f) (fun x -> v x)
               (fun _ -> True)    (fun h0 x h1 -> h0 (vexists v f) == f x (h1 (v x)))


(* [vdept] : [vdep] with a cast on the second component *)
(* TODO ? use on_dom / restricted_t *)

val vdept_sl (v : vprop) (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x}))
  : Mem.slprop u#1

val vdept_sel (v : vprop) (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x}))
  : selector (dtuple2 (t_of v) dt) (vdept_sl v #dt p)

[@@__steel_reduce__]
let vdept' (v : vprop) (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x})) = {
  hp  = vdept_sl  v #dt p;
  t   = dtuple2 (t_of v) dt;
  sel = vdept_sel v #dt p
}
unfold let vdept (v : vprop) (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x})) : vprop
  = VUnit (vdept' v #dt p)

val interp_vdept_sl (v : vprop) (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x}))
                    (m: Mem.mem)
  : Lemma Mem.(interp (vdept_sl v #dt p) m
               <==> (interp (hp_of v) m /\ interp (hp_of v `star` hp_of (p (sel_of v m))) m))

val vdept_sel_eq (v : vprop) (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x}))
                 (m: Mem.hmem (vdept_sl v #dt p))
  : Lemma Mem.(
      interp (hp_of v) m /\
     (let x = sel_of v m in
      interp (hp_of (p x)) m /\
      vdept_sel v p m == (| x, sel_of (p x) m |) ))

val intro_vdept (#opened:inames) (v: vprop) (q: vprop)
                (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x}))
: SteelGhost unit opened
    (v `star` q) (fun _ -> vdept v #dt p)
    (requires fun h -> q == p (h v))
    (ensures fun h _ h' ->
      let x2 = h' (vdept v #dt p) in
      q == p (h v) /\
      dfst x2 == (h v) /\
      dsnd x2 == (h q)
    )

val elim_vdept (#opened:inames) (v: vprop) (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x}))
: SteelGhost (G.erased (t_of v)) opened
  (vdept v p)
  (fun res -> v `star` p (G.reveal res))
  (requires fun _ -> True)
  (ensures fun h res h' ->
      let fs = h' v in
      let sn : dt (G.reveal res) = h' (p (G.reveal res)) in
      let x2 = h (vdept v #dt p) in
      G.reveal res == fs /\
      dfst x2 == fs /\
      dsnd x2 == sn
  )


(* [gwand] : Magic wand implemented with a SteelGhost function *)

[@@erasable]
noeq type gwand (src : vprop) (trg : vprop) : Type = {
  vp  : vprop;
  req : normal (t_of src) -> GTot prop;
  ens : normal (t_of src) -> normal (t_of trg) -> GTot prop;
  elim_wand : (#opened : Mem.inames) -> unit -> (* TODO? req on opened *)
              SteelGhost unit opened
                (vp `star` src) (fun () -> trg)
                (fun h0 -> req (h0 src)) (fun h0 () h1 -> ens (h0 src) (h1 trg))
}

val intro_gwand (#opened : Mem.inames)
  (vp : vprop) (sl : normal (t_of vp)) (* ALT?: h0 vp *)
  (src trg : vprop)
  (req : normal (t_of src) -> GTot prop)
  (ens : normal (t_of src) -> normal (t_of trg) -> GTot prop)
  (func : (opened' : Mem.inames) ->
    SteelGhost unit opened'
      (vp `star` src) (fun () -> trg)
      (fun h0 -> h0 vp == sl /\ req (h0 src))
      (fun h0 () h1 -> ens (h0 src) (h1 trg)))
  : SteelGhost (gwand src trg) opened
      vp (fun wd -> wd.vp)
      (requires fun h0 -> h0 vp == sl)
      (ensures  fun _ wd h1 ->
        wd.req == req /\ wd.ens == ens)

val elim_gwand (#opened : Mem.inames) (#src0 #trg0 : vprop) (wd : gwand src0 trg0)
               (src trg : vprop)
  : SteelGhost unit opened
      (wd.vp `star` src) (fun () -> trg)
      (requires fun h0 ->
         src0 == src /\ trg0 == trg /\
         wd.req (h0 src))
      (ensures  fun h0 () h1 ->
         src0 == src /\ trg0 == trg /\
         wd.ens (h0 src) (h1 trg))


(* [aptr] : abstract references *)

inline_for_extraction noextract noeq
type aptr' (t : Type) = {
  vp      : vprop;
  of_sel  : normal (t_of vp) -> GTot t;
  set_sel : normal (t_of vp) -> (x : t) ->
            Ghost (normal (t_of vp)) (requires True) (ensures fun rt -> of_sel rt == x);
  read    : unit -> Steel t vp (fun _ -> vp) (requires fun _ -> True)
                   (ensures fun h0 x h1 -> frame_equalities vp h0 h1 /\ x == of_sel (h0 vp));
  write   : (x : t) -> Steel unit vp (fun _ -> vp) (requires fun _ -> True)
                   (ensures fun h0 () h1 -> h1 vp == set_sel (h0 vp) x)
}

inline_for_extraction noextract
type aptr (t : Type) = p:aptr' t {
     (forall (s : normal (t_of p.vp)) (x0 x1 : t) . {:pattern (p.set_sel (p.set_sel s x0) x1)}
        p.set_sel (p.set_sel s x0) x1 == p.set_sel s x1) /\
     (forall (s : normal (t_of p.vp)) . {:pattern (p.set_sel s (p.of_sel s))}
        p.set_sel s (p.of_sel s) == s)
  }

[@@ __steel_reduce__]
let sel_aptr (#t:Type) (#p:vprop) (x:aptr t)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (x.vp) /\ True)})
  : GTot (normal (t_of x.vp))
  = h x.vp

[@@ __steel_reduce__]
let aptr_val (#t:Type) (#p:vprop) (x:aptr t)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (x.vp) /\ True)})
  : GTot t
  = x.of_sel (h x.vp)

[@@ __steel_reduce__]
let aptr_updt (#t:Type) (#p #q:vprop) (x:aptr t) (v:t)
  (h0:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (x.vp) /\ True)})
  (h1:rmem q{FStar.Tactics.with_tactic selector_tactic (can_be_split q (x.vp) /\ True)})
  : prop
  = h1 x.vp == x.set_sel (h0 x.vp) v


[@@ __steel_reduce__]
inline_for_extraction noextract
let aptr_of_vptr (#t : Type) (r : ref t) : Tot (aptr t) = {
  vp      = vptr r;
  of_sel  = (fun x   -> (x <: t));
  set_sel = (fun _ x -> x);
  read    = (fun () -> read r);
  write   = (fun x  -> write r x)
}


inline_for_extraction noextract noeq
type get_set_t' (c t : Type) = {
  get : c -> Tot t;
  set : c -> t -> Tot c;
}

inline_for_extraction noextract
type get_set_t (c t : Type) = p:get_set_t' c t {
     (forall (s : c) (x : t) . {:pattern (p.get (p.set s x))}
        p.get (p.set s x) == x) /\
     (forall (s : c) (x0 x1 : t) . {:pattern (p.set (p.set s x0) x1)}
        p.set (p.set s x0) x1 == p.set s x1) /\
      (forall (s : c) . {:pattern (p.set s (p.get s))}
        p.set s (p.get s) == s)
  }

[@@ __steel_reduce__]
inline_for_extraction noextract
let aptr_of_get_set (#c #t : Type) ($p : get_set_t c t) (r : ref c) : Tot (aptr t) = {
  vp      = vptr r;
  of_sel  = (fun x   -> p.get x);
  set_sel = (fun s x -> p.set s x);
  read    = (fun () -> let s = read r in p.get s);
  write   = (fun x  -> let s = read r in write r (p.set s x))
}
