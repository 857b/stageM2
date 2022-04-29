module Experiment.Repr.Fun

(* TODO? (a : Type)  --->  (ts : ty_list) *)

noeq
type prog_tree : (a : Type) -> Type =
  | Tnew   : (a : Type) -> prog_tree a
  | Tasrt  : (p : prop) -> prog_tree unit
  | Tasum  : (p : prop) -> prog_tree unit
  | Tret   : (a : Type) -> (x : a) -> prog_tree a
  | Tbind  : (a : Type) -> (b : Type) ->
             (f : prog_tree a) -> (g : a -> prog_tree b) ->
             prog_tree b
  | TbindP : (a : Type) -> (b : Type) ->
             (wp : pure_wp a) -> (x : unit -> PURE a wp) -> (g : a -> prog_tree b) ->
             prog_tree b

let return (#a : Type) (x : a) : prog_tree a
  = Tret a x

let bind (#a #b : Type) (f : prog_tree a) (g : a -> prog_tree b) : prog_tree b
  = Tbind a b f g


let rec tree_req (#a : Type) (t : prog_tree a)
  : Tot pure_pre (decreases t)
  = match t with
  | Tnew   _          -> True
  | Tasrt  p          -> p
  | Tasum  _          -> True
  | Tret   _ _        -> True
  | Tbind  a _ f g    -> tree_req f /\ (forall (x : a) . tree_ens f x ==> tree_req (g x))
  | TbindP a _ wp _ g -> wp (fun x -> tree_req (g x)) /\ True

and tree_ens (#a : Type) (t : prog_tree a)
  : Tot (pure_post a) (decreases t)
  = match t with
  | Tnew   _          -> fun _  -> True
  | Tasrt  p          -> fun () -> True (* p ?*)
  | Tasum  p          -> fun () -> p
  | Tret   _ x        -> fun r  -> r == x
  | Tbind  a _ f g    -> fun y  -> exists (x : a) . tree_ens f x /\ tree_ens (g x) y
  | TbindP a _ wp _ g -> fun y -> as_requires wp /\ (exists (x : a) . as_ensures wp x /\ tree_ens (g x) y)


module MP = FStar.Monotonic.Pure
module T  = FStar.Tactics
module U  = Learn.Util
open FStar.Classical.Sugar


let rec tree_wp (#a : Type) (t : prog_tree a)
  : Tot (pure_wp a) (decreases t)
  = match t with
  | Tnew  a           -> MP.as_pure_wp (fun pt -> forall (x : a) . pt x)
  | Tasrt p           -> MP.as_pure_wp (fun pt -> p /\ (p ==> pt ()))
  | Tasum p           -> MP.as_pure_wp (fun pt -> p ==> pt ())
  | Tret  _ x         -> MP.as_pure_wp (fun pt -> pt x)
  | Tbind a _ f g     -> MP.elim_pure_wp_monotonicity_forall ();
                        MP.as_pure_wp (fun pt -> tree_wp f (fun (x : a) -> tree_wp (g x) pt))
  | TbindP a _ wp _ g -> MP.elim_pure_wp_monotonicity_forall ();
                        MP.as_pure_wp (fun pt -> wp (fun (x : a) -> tree_wp (g x) pt))

let rec tree_wp_sound (#a : Type) (t : prog_tree a) (post : pure_post a)
  : Lemma (requires tree_wp t post)
          (ensures  tree_req t /\ (forall (x : a) . tree_ens t x ==> post x))
  = match t with
  | Tnew _ | Tasrt _ | Tasum _ | Tret _ _ -> ()
  | Tbind a b f g ->
      let post1 (x : a) = tree_wp (g x) post in
      assert (tree_wp (Tbind a b f g) post == tree_wp f post1) by T.(trefl ());
      tree_wp_sound f post1;
      introduce forall (x : a) . tree_wp (g x) post ==> (tree_req (g x) /\ (forall (y : b) . tree_ens (g x) y ==> post y))
        with introduce _ ==> _ with _ . tree_wp_sound (g x) post
  | TbindP a b wp xf g ->
      let post1 (x : a) = tree_wp (g x) post in
      let req1  (x : a) = tree_req (g x)     in
      assert (tree_wp (TbindP a b wp xf g) post == wp post1) by T.(trefl ());
      MP.elim_pure_wp_monotonicity wp;
      introduce forall (x : a) . post1 x ==> (req1 x /\ (forall (y : b) . tree_ens (g x) y ==> post y))
        with introduce _ ==> _ with _ . tree_wp_sound (g x) post;
      assert (tree_req (TbindP a b wp xf g) == (wp req1 /\ True)) by T.(trefl ());
      U.prop_equal (fun p -> p) (wp req1 /\ True) (tree_req (TbindP a b wp xf g))
