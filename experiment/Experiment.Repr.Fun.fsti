module Experiment.Repr.Fun

module U  = Learn.Util
module T = FStar.Tactics
module MP = FStar.Monotonic.Pure


(*** Parameter *)

/// [tys] describes a family of types, indexed by [t]. Those types are used for the returned values of programs.
/// - [v] map the index to the associated type
/// - [r ty] is a "concrete" representation of [v ty]
/// - [unit] should be associated to a type with an unique element [emp]
/// - [all] and [ex] are representations of the universal and existential quantification. They are used when
///   generating the VC. They must be equivalent to a quantification on [v ty]
noeq
type tys' = {
  t : Type u#t;
  v : t -> Type u#v;
  r : t -> Type u#r;
  v_of_r : (#ty : t) -> r ty -> v ty;
  r_of_v : (#ty : t) -> v ty -> r ty;
  unit : t;
  emp  : v unit;
  all  : (ty : t) -> (v ty -> Type0) -> Type0;
  ex   : (ty : t) -> (v ty -> Type0) -> Type0; 
}

let tys_hyp (s : tys') : prop =
  (forall (ty : s.t) (x : s.v ty) . {:pattern (s.v_of_r (s.r_of_v x))} s.v_of_r (s.r_of_v x) == x) /\
  (forall (x : s.v s.unit) . x == s.emp) /\
  (forall (ty : s.t) (f : s.v ty -> Type0) . {:pattern (s.all ty f)} s.all ty f <==> (forall (x : s.v ty) . f x)) /\
  (forall (ty : s.t) (f : s.v ty -> Type0) . {:pattern (s.ex  ty f)} s.ex  ty f <==> (exists (x : s.v ty) . f x))

type tys = s : tys' {tys_hyp s}

/// [tys_lam] is used to unpack the values when building a function.
/// Since we need to use it for post-conditions and trees we requires two versions (because of universes and Ghost
/// effect).
noeq
type tys_lam' (s : tys u#t u#v u#r) = {
  lam_prop : (#src : s.t) -> (f : pure_post (s.v src)) -> pure_post (s.v src);
  lam_tree : (#src : s.t) -> (#trg : Type u#a) -> (f : s.v src -> trg) -> (s.v src -> trg);
}

let tys_lam_id (#s : tys) (lm : tys_lam' s) : prop =
  (forall (src : s.t) (f : pure_post (s.v src)) . lm.lam_prop f == (fun (x : s.v src) -> f x)) /\
  (forall (src : s.t) (trg : Type) (f : s.v src -> trg) . lm.lam_tree f == (fun (x : s.v src) -> f x))

type tys_lam (s : tys) = lm : tys_lam' s {tys_lam_id lm}

/// Canonical instantiation of [tys]

unfold
let can_tys' : tys' u#(v+1) u#v u#v = {
  t = Type u#v;
  v = (fun ty -> ty);
  r = (fun ty -> ty);
  v_of_r = (fun x -> x);
  r_of_v = (fun x -> x);
  unit = U.unit';
  emp  = U.Unit';
  all  = (fun ty p -> forall (x : ty) . p x);
  ex   = (fun ty p -> exists (x : ty) . p x)
}

let can_tys : tys u#(v+1) u#v u#v =
  (**) assert (tys_hyp can_tys') by T.(norm [delta]; smt ());
  can_tys'

unfold
let can_lam' (s : tys) : tys_lam' s = {
  lam_prop = (fun f -> (fun x -> f x));
  lam_tree = (fun f -> (fun x -> f x))
}

let can_lam (s : tys) : tys_lam s =
  let lm = can_lam' s in
  (**) assert (forall (src : s.t) (f : pure_post (s.v src)) .
  (**)           lm.lam_prop f == (fun (x : s.v src) -> f x))
  (**)  by T.(let _ = forall_intros () in trefl ());
  (**) assert (forall (src : s.t) (trg : Type) (f : s.v src -> trg) .
  (**)           lm.lam_tree #src #trg f == (fun (x : s.v src) -> f x))
  (**)   by T.(let _ = forall_intros () in trefl ());
  lm


(*** [prog_tree] *)

noeq
type prog_tree (#s : tys u#t u#v u#r) : s.t -> Type u#(max t v r a + 1) =
  | Tnew   : (a : s.t) -> prog_tree #s a
  | Tasrt  : (p : prop) -> prog_tree #s s.unit
  | Tasum  : (p : prop) -> prog_tree #s s.unit
  | Tspec  : (a : s.t) -> (pre : pure_pre) -> (post : pure_post (s.v a)) ->
             prog_tree #s a
  | Tret   : (a : s.t) -> (x : s.r a) -> prog_tree #s a
  | Tbind  : (a : s.t) -> (b : s.t) ->
             (f : prog_tree #s a) -> (g : s.v a -> prog_tree #s b) ->
             prog_tree #s b
  // having [a] of type [Type u#a] instead of [s.t] allows it to be in a different universe
  | TbindP : (a : Type u#a) -> (b : s.t) ->
             (wp : pure_wp a) -> (g : a -> prog_tree #s b) ->
             prog_tree #s b
  | Tif    : (a : s.t) -> (guard : bool) ->
             (thn : prog_tree #s a) -> (els : prog_tree #s a) ->
             prog_tree #s a
  | Twp    : (a : s.t) -> (wp : pure_wp (s.v a)) ->
             prog_tree #s a

unfold
let return (#s : tys) (#a : s.t) ($x : s.v a) : prog_tree #s a
  = Tret a (s.r_of_v x)

unfold
let bind (#s : tys) (#a #b : s.t) (f : prog_tree #s a) (g : s.v a -> prog_tree #s b) : prog_tree #s b
  = Tbind a b f g


(***** Shape *)

type shape_tree : Type0 =
  | Snew | Sasrt | Sasum | Sspec | Swp
  | Sret   : (smp_ret : bool) -> shape_tree
  | Sbind  : (f : shape_tree) -> (g : shape_tree) -> shape_tree
  | SbindP : (g : shape_tree) -> shape_tree
  | Sif    : (thn : shape_tree) -> (els : shape_tree) -> shape_tree

[@@ strict_on_arguments [2]] (* strict on t *)
let rec prog_has_shape (#ts : tys) (#a : ts.t) (t : prog_tree u#t u#v u#r u#a #ts a) (s : shape_tree)
  : Tot prop (decreases t)
  = match t returns prop with
  | Tnew _          -> s == Snew
  | Tasrt _         -> s == Sasrt
  | Tasum _         -> s == Sasum
  | Tspec _ _ _     -> s == Sspec
  | Tret  _ _       -> exists (smp_ret : bool) .
                      s == Sret smp_ret
  | Tbind a _ f g   -> exists (s_f s_g : shape_tree) .
                      s == Sbind s_f s_g /\
                      prog_has_shape f s_f /\
                     (forall (x : ts.v a) . prog_has_shape (g x) s_g)
  | TbindP a _ _ g  -> exists (s_g : shape_tree) .
                       s == SbindP s_g /\
                      (forall (x : a) . prog_has_shape (g x) s_g)
  | Tif _ _ thn els -> exists (s_thn : shape_tree) (s_els : shape_tree) .
                      s == Sif s_thn s_els /\
                      prog_has_shape thn s_thn /\
                      prog_has_shape els s_els
  | Twp _ _         -> s == Swp

let rec prog_has_shape' (#ts : tys) (#a : ts.t) (t : prog_tree u#t u#v u#r u#a #ts a) (s : shape_tree)
  : Pure prop (requires True) (ensures fun p -> p <==> prog_has_shape t s) (decreases t)
  = match t returns prop with
  | Tnew _          -> s == Snew
  | Tasrt _         -> s == Sasrt
  | Tasum _         -> s == Sasum
  | Tspec _ _ _     -> s == Sspec
  | Tret  _ _       -> (match s with
                      | Sret _ -> True
                      | _ -> False)
  | Tbind a _ f g   -> (match s with
                      | Sbind s_f s_g -> 
                          prog_has_shape' f s_f /\
                         (forall (x : ts.v a) . prog_has_shape' (g x) s_g)
                      | _ -> False)
  | TbindP a _ _ g  -> (match s with
                      | SbindP s_g ->
                         (forall (x : a) . prog_has_shape' (g x) s_g)
                      | _ -> False)
  | Tif _ _ thn els -> (match s with
                      | Sif s_thn s_els ->
                         prog_has_shape' thn s_thn /\
                         prog_has_shape' els s_els
                      | _ -> False)
  | Twp _ _         -> s == Swp


type prog_shape (#ts : tys) (#a : ts.t) (t : prog_tree #ts a) =
  s : shape_tree { prog_has_shape t s }


(*** Semantics *)

/// We do not ensure [tree_req f] in the post-condition of [Tbind]. This is equivalent (assuming the
/// pre-condition, as in [equiv]) but it is simpler for reasoning about some program transformations.
/// For instance, if one ensures [tree_req f] for the bind, the post-condition of `let x = f in x` is equivalent
/// to the post-condition of `f` only when the pre-condition holds.
/// The same holds for [as_requires wp] in the post-condition of [TbindP].

[@@ strict_on_arguments [2]] (* strict on t *)
let rec tree_req (#s : tys) (#a : s.t) (t : prog_tree #s a)
  : Tot pure_pre (decreases t)
  = match t with
  | Tnew   _            -> True
  | Tasrt  p            -> p
  | Tasum  _            -> True
  | Tspec  _ pre _      -> pre
  | Tret   _ _          -> True
  | Tbind  a b f g      -> tree_req f /\ s.all a (fun (x : s.v a) -> tree_ens f x ==> tree_req (g x))
  | TbindP a _ wp g     -> wp (fun x -> tree_req (g x))
  | Tif    a gd thn els -> if gd then tree_req thn else tree_req els
  | Twp    a wp         -> as_requires wp

and tree_ens (#s : tys) (#a : s.t) (t : prog_tree #s a)
  : Tot (pure_post (s.v a)) (decreases t)
  = match t with
  | Tnew   _            -> fun _  -> True
  | Tasrt  p            -> fun _(*()*) -> True (* p ?*)
  | Tasum  p            -> fun _(*()*) -> p
  | Tspec  a _ post     -> post
  | Tret   _ x          -> fun r  -> r == s.v_of_r x
  | Tbind  a _ f g      -> fun y  -> s.ex a (fun (x : s.v a) -> tree_ens f x /\ tree_ens (g x) y)
  | TbindP a _ wp g     -> fun y -> (exists (x : a) . as_ensures wp x /\ tree_ens (g x) y)
  | Tif    a gd thn els -> fun y -> if gd then tree_ens thn y else tree_ens els y
  | Twp    a wp         -> as_ensures wp


(***** Equivalence *)

let equiv (#s : tys) (#a : s.t) (f g : prog_tree #s a) : prop =
  (tree_req f <==> tree_req g) /\
  (tree_req f ==> (forall (x : s.v a) . tree_ens f x <==> tree_ens g x))


let equiv_refl (#s : tys) (#a : s.t) (f : prog_tree #s a)
  : Lemma (equiv f f)
  = ()

let equiv_sym (#s : tys) (#a : s.t) (f g : prog_tree #s a)
  : Lemma (requires equiv f g) (ensures equiv g f)
  = ()

let equiv_trans (#s : tys) (#a : s.t) (f g h : prog_tree #s a)
  : Lemma (requires equiv f g /\ equiv g h) (ensures equiv f h)
  = ()

val equiv_Tbind
      (#s : tys) (#a #b : s.t)
      (f f' : prog_tree a) (g g' : (x : s.v a) -> prog_tree b)
      (eq_f : squash (equiv f f')) (eq_g : (x : s.v a) -> squash (equiv (g x) (g' x)))
  : Lemma (equiv (Tbind a b f g) (Tbind a b f' g'))

val equiv_TbindP
      (#s : tys) (#a : Type) (#b : s.t) (wp : pure_wp a)
      (g g' : (x : a) -> prog_tree b)
      (eq_g : (x : a) -> squash (equiv (g x) (g' x)))
  : Lemma (equiv (TbindP a b wp g) (TbindP a b wp g'))

val equiv_Tif
      (#s : tys) (#a : s.t) (guard : bool)
      (thn thn' : prog_tree a) (els els' : prog_tree a)
      (eq_thn : squash (equiv thn thn')) (eq_els : squash (equiv els els'))
  : Lemma (equiv (Tif a guard thn els) (Tif a guard thn' els'))

val equiv_Tbind_assoc_Tbind
      (#s : tys) (#a #b #c : s.t)
      (f : prog_tree #s a) (g : (x : s.v a) -> prog_tree b) (h : (y : s.v b) -> prog_tree c)
  : Lemma (equiv (bind (bind f g) h) (bind f (fun x -> bind (g x) h)))

(**) val __end_section_equiv : unit


(***** Weakest-precondition *)

[@@ strict_on_arguments [2]] (* strict on t *)
let rec tree_wp (#s : tys) (#a : s.t) (t : prog_tree #s a)
  : Tot (pure_wp (s.v a)) (decreases t)
  = match t with
  | Tnew  a          -> MP.as_pure_wp (fun pt -> s.all a (fun (x : s.v a) -> pt x))
  | Tasrt p          -> MP.as_pure_wp (fun pt -> p /\ (p ==> pt s.emp))
  | Tasum p          -> MP.as_pure_wp (fun pt -> p ==> pt s.emp)
  | Tspec a pre post -> MP.as_pure_wp (fun pt -> pre /\ s.all a (fun (x : s.v a) -> post x ==> pt x))
  | Tret  _ x        -> MP.as_pure_wp (fun pt -> pt (s.v_of_r x))
  | Tbind a _ f g    -> MP.elim_pure_wp_monotonicity_forall ();
                       MP.as_pure_wp (fun pt -> tree_wp f (fun (x : s.v a) -> tree_wp (g x) pt))
  | TbindP a _ wp g  -> MP.elim_pure_wp_monotonicity_forall ();
                       MP.as_pure_wp (fun pt -> wp (fun (x : a) -> tree_wp (g x) pt))
  | Tif a gd thn els -> MP.elim_pure_wp_monotonicity_forall ();
                       MP.as_pure_wp (fun pt -> (  gd  ==> tree_wp thn pt) /\
                                             ((~gd) ==> tree_wp els pt))
  | Twp a wp         -> wp

val tree_wp_sound (#s : tys) (#a : s.t) (t : prog_tree #s a) (post : pure_post (s.v a))
  : Lemma (requires tree_wp t post)
          (ensures  tree_req t /\ (forall (x : s.v a) . tree_ens t x ==> post x))


(*** Returns elimination *)

/// This transformation aims to eliminate the [Tret] introduced by previous transformations (Steel.Repr.M ->
/// Steel.Repr.ST -> Steel.Repr.SF).
/// We do not try to handle all possible simplifications but rather to have a transformation that works in our cases.
/// It currently performs a binders flattening (similar to the one on Steel.Repr.ST), with a special handling of
/// returns in order to be able to push them below [TbindP].
/// We only simplify the returns marked with [smp_ret] in the shape, that is, the returns introduced by the
/// previous transformations. (TODO: test)
/// The shape is also used to detect return on the right of bind.

noeq
type elim_returns_k (st : tys) (a a1 : st.t) =
  | ERetKfun : (k : st.v a -> st.v a1) -> elim_returns_k st a a1
  | ERetKtrm : (k : st.v a -> prog_tree #st a1) -> elim_returns_k st a a1

let elim_returns_k_ret (#st : tys) (#a #a1 : st.t) (f : st.v a -> st.v a1) (x : st.v a)
  : prog_tree #st a1
  = Tret a1 (st.r_of_v (f x))

let elim_returns_k_trm (#st : tys) (#a #a1 : st.t) (k : elim_returns_k st a a1)
  : st.v a -> prog_tree #st a1
  = match k with
  | ERetKfun kf -> elim_returns_k_ret kf
  | ERetKtrm kt -> kt

let rec elim_returns
      (#st : tys) (lm : tys_lam u#t u#v u#r u#(max t v r a + 1) st)
      (#a : st.t) (t : prog_tree u#t u#v u#r u#a #st a) (s : prog_shape t)
  : Tot (prog_tree u#t u#v u#r u#a #st a) (decreases %[t; 1])
  = elim_returns_aux lm t s (ERetKfun id)

and elim_returns_aux
      (#st : tys) (lm : tys_lam u#t u#v u#r u#(max t v r a + 1) st)
      (#a : st.t) (t : prog_tree u#t u#v u#r u#a #st a) (s : prog_shape t)
      (#a1 : st.t) (k : elim_returns_k st a a1)
  : Tot (prog_tree u#t u#v u#r u#a #st a1) (decreases %[t; 0])
  =
  let bind (#a : st.t) (#b : st.t) (f : prog_tree #st a) (g : st.v a -> prog_tree #st b) : prog_tree #st b
    = Tbind a b f (lm.lam_tree g)
  in
  match t with
  | Tnew _ | Tasrt _ | Tasum _ | Twp _ _ ->
         bind t (elim_returns_k_trm k)
  | Tspec a pre post ->
         bind (Tspec a pre (lm.lam_prop post)) (elim_returns_k_trm k)
  | Tret a x ->
         let Sret smp_ret = s in
         if smp_ret then elim_returns_k_trm k (st.v_of_r x)
         else begin match k with
         | ERetKfun kf -> Tret a1 (st.r_of_v (kf (st.v_of_r x)))
         | ERetKtrm kt -> bind (Tret a x) kt
         end
  | Tbind a b f g ->
         let Sbind s_f s_g = s in
         begin match s_g, k with
         | Sret true, ERetKfun kf ->
               let k1 (x : st.v a) = kf (st.v_of_r (Tret?.x (g x))) in
               elim_returns_aux lm f s_f (ERetKfun k1)
         | _ -> let k1 (x : st.v a) = elim_returns_aux lm (g x) s_g k in
               elim_returns_aux lm f s_f (ERetKtrm k1)
         end
  | TbindP a b wp g ->
         let SbindP s_g = s in
         begin match k with
         | ERetKfun kf -> TbindP a a1 wp (fun (x : a) -> elim_returns_aux lm (g x) s_g (ERetKfun kf))
         | ERetKtrm kt -> bind #b #a1 (TbindP a b wp (fun (x : a) -> elim_returns lm (g x) s_g)) kt
         end
  | Tif a guard thn els ->
        let Sif s_thn s_els = s in
        bind (Tif a guard (elim_returns lm thn s_thn) (elim_returns lm els s_els)) (elim_returns_k_trm k)

val elim_returns_equiv
      (#st : tys) (lm : tys_lam u#t u#v u#r u#(max t v r a + 1) st)
      (#a : st.t) (t : prog_tree u#t u#v u#r u#a #st a) (s : prog_shape t)
  : Lemma (equiv (elim_returns lm t s) t)

val elim_returns_equiv_aux
      (#st : tys) (lm : tys_lam u#t u#v u#r u#(max t v r a + 1) st)
      (#a : st.t) (t : prog_tree u#t u#v u#r u#a #st a) (s : prog_shape t)
      (#a1 : st.t) (k : elim_returns_k st a a1)
  : Lemma (equiv (elim_returns_aux lm t s k) (Tbind a a1 t (elim_returns_k_trm k)))
