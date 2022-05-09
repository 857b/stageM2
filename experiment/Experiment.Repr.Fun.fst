module Experiment.Repr.Fun

module U = Learn.Util

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

type tys = s : tys' {
  (forall (ty : s.t) (x : s.v ty) . {:pattern (s.v_of_r (s.r_of_v x))} s.v_of_r (s.r_of_v x) == x) /\
  (forall (x : s.v s.unit) . x == s.emp) /\
  (forall (ty : s.t) (f : s.v ty -> Type0) . {:pattern (s.all ty f)} s.all ty f <==> (forall (x : s.v ty) . f x)) /\
  (forall (ty : s.t) (f : s.v ty -> Type0) . {:pattern (s.ex  ty f)} s.ex  ty f <==> (exists (x : s.v ty) . f x))
}

let can_tys : tys u#(v+1) u#v u#v = {
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

noeq
type prog_tree (s : tys u#t u#v u#r) : s.t -> Type u#(max t v r a + 1) =
  | Tnew   : (a : s.t) -> prog_tree s a
  | Tasrt  : (p : prop) -> prog_tree s s.unit
  | Tasum  : (p : prop) -> prog_tree s s.unit
  | Tspec  : (a : s.t) -> (pre : pure_pre) -> (post : pure_post (s.v a)) ->
             prog_tree s a
  | Tret   : (a : s.t) -> (x : s.r a) -> prog_tree s a
  | Tbind  : (a : s.t) -> (b : s.t) ->
             (f : prog_tree s a) -> (g : s.v a -> prog_tree s b) ->
             prog_tree s b
  (* [a] could be of type [s.t] *)
  | TbindP : (a : Type u#a) -> (b : s.t) ->
             (wp : pure_wp a) -> (x : unit -> PURE a wp) -> (g : a -> prog_tree s b) ->
             prog_tree s b


let return (#s : tys) (#a : s.t) ($x : s.v a) : prog_tree s a
  = Tret a (s.r_of_v x)

let bind (#s : tys) (#a #b : s.t) (f : prog_tree s a) (g : s.v a -> prog_tree s b) : prog_tree s b
  = Tbind a b f g

/// We do not ensure [tree_req f] in the post-condition of [Tbind]. This is equivalent (assuming the
/// pre-condition, as in [equiv]) but it is simpler for reasoning about some program transformations.
/// For instance, if one ensures [tree_req f] for the bind, the post-condition of `let x = f in x` is equivalent
/// to the post-condition of `f` only when the pre-condition holds.
/// The same holds for [as_requires wp] in the post-condition of [TbindP].

let rec tree_req (#s : tys) (#a : s.t) (t : prog_tree s a)
  : Tot pure_pre (decreases t)
  = match t with
  | Tnew   _          -> True
  | Tasrt  p          -> p
  | Tasum  _          -> True
  | Tspec  _ pre _    -> pre
  | Tret   _ _        -> True
  | Tbind  a b f g    -> tree_req f /\ s.all a (fun (x : s.v a) -> tree_ens f x ==> tree_req (g x))
  | TbindP a _ wp _ g -> wp (fun x -> tree_req (g x))

and tree_ens (#s : tys) (#a : s.t) (t : prog_tree s a)
  : Tot (pure_post (s.v a)) (decreases t)
  = match t with
  | Tnew   _          -> fun _  -> True
  | Tasrt  p          -> fun _(*()*) -> True (* p ?*)
  | Tasum  p          -> fun _(*()*) -> p
  | Tspec  a _ post   -> post
  | Tret   _ x        -> fun r  -> r == s.v_of_r x
  | Tbind  a _ f g    -> fun y  -> s.ex a (fun (x : s.v a) -> tree_ens f x /\ tree_ens (g x) y)
  | TbindP a _ wp _ g -> fun y -> (exists (x : a) . as_ensures wp x /\ tree_ens (g x) y)


(*** Equivalence *)

let equiv (#s : tys) (#a : s.t) (f g : prog_tree s a) : prop =
  (tree_req f <==> tree_req g) /\
  (tree_req f ==> (forall (x : s.v a) . tree_ens f x <==> tree_ens g x))


let equiv_refl (#s : tys) (#a : s.t) (f : prog_tree s a)
  : Lemma (equiv f f)
  = ()

let equiv_sym (#s : tys) (#a : s.t) (f g : prog_tree s a)
  : Lemma (requires equiv f g) (ensures equiv g f)
  = ()

let equiv_trans (#s : tys) (#a : s.t) (f g h : prog_tree s a)
  : Lemma (requires equiv f g /\ equiv g h) (ensures equiv f h)
  = ()


(*** Weakest-precondition *)

module MP = FStar.Monotonic.Pure
module T  = FStar.Tactics
module U  = Learn.Util
open FStar.Classical.Sugar


let rec tree_wp (#s : tys) (#a : s.t) (t : prog_tree s a)
  : Tot (pure_wp (s.v a)) (decreases t)
  = match t with
  | Tnew  a           -> MP.as_pure_wp (fun pt -> s.all a (fun (x : s.v a) -> pt x))
  | Tasrt p           -> MP.as_pure_wp (fun pt -> p /\ (p ==> pt s.emp))
  | Tasum p           -> MP.as_pure_wp (fun pt -> p ==> pt s.emp)
  | Tspec a pre post  -> MP.as_pure_wp (fun pt -> pre /\ s.all a (fun (x : s.v a) -> post x ==> pt x))
  | Tret  _ x         -> MP.as_pure_wp (fun pt -> pt (s.v_of_r x))
  | Tbind a _ f g     -> MP.elim_pure_wp_monotonicity_forall ();
                        MP.as_pure_wp (fun pt -> tree_wp f (fun (x : s.v a) -> tree_wp (g x) pt))
  | TbindP a _ wp _ g -> MP.elim_pure_wp_monotonicity_forall ();
                        MP.as_pure_wp (fun pt -> wp (fun (x : a) -> tree_wp (g x) pt))

let rec tree_wp_sound (#s : tys) (#a : s.t) (t : prog_tree s a) (post : pure_post (s.v a))
  : Lemma (requires tree_wp t post)
          (ensures  tree_req t /\ (forall (x : s.v a) . tree_ens t x ==> post x))
          (decreases t)
  = match t with
  | Tnew _ | Tasrt _ | Tasum _ | Tret _ _ | Tspec _ _ _ -> ()
  | Tbind a b f g ->
      let post1 (x : s.v a) = tree_wp (g x) post in
      assert (tree_wp (Tbind a b f g) post == tree_wp f post1) by T.(trefl ());
      tree_wp_sound f post1;
      introduce forall (x : s.v a) . tree_wp (g x) post ==> (tree_req (g x) /\ (forall (y : s.v b) . tree_ens (g x) y ==> post y))
        with introduce _ ==> _ with _ . tree_wp_sound (g x) post
  | TbindP a b wp xf g ->
      let post1 (x : a) = tree_wp (g x) post in
      let req1  (x : a) = tree_req (g x)     in
      assert (tree_wp (TbindP a b wp xf g) post == wp post1) by T.(trefl ());
      MP.elim_pure_wp_monotonicity wp;
      introduce forall (x : a) . post1 x ==> (req1 x /\ (forall (y : s.v b) . tree_ens (g x) y ==> post y))
        with introduce _ ==> _ with _ . tree_wp_sound (g x) post;
      assert (tree_req (TbindP a b wp xf g) == (wp req1)) by T.(trefl ());
      U.prop_equal (fun p -> p) (wp req1) (tree_req (TbindP a b wp xf g))
