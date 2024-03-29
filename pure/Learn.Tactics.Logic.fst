module Learn.Tactics.Logic

module U = Learn.Util
module L = FStar.List.Pure

open FStar.Tactics


let iff_refl (p : Type) : squash (p <==> p)
  = ()

let rew_iff_left (p0 p1 q : Type)
    (_ : squash (p0 <==> p1))
    (_ : squash (p1  <==> q))
  : squash (p0 <==> q)
  = ()

let rew_iff_right (p q0 q1 : Type)
    (_ : squash (q0 <==> q1))
    (_ : squash (p  <==> q1))
  : squash (p <==> q0)
  = ()

let conj_morph_iff (p0 q0 p1 q1 : Type0)
    (_ : squash (p0 <==> p1))
    (eq_q : squash (p0 /\ p1) -> squash (q0 <==> q1))
  : squash ((p0 /\ q0) <==> (p1 /\ q1))
  = FStar.Classical.Sugar.implies_intro _ _ eq_q

let forall_morph_iff (#a : Type) (p0 p1 : a -> Type0)
      (prf : (x : a) -> squash (p0 x <==> p1 x))
  : squash ((forall (x : a) . p0 x) <==> (forall (x : a) . p1 x))
  = FStar.Classical.forall_intro_squash_gtot prf

let exists_morph_iff (#a : Type) (p0 p1 : a -> Type0)
      (prf : (x : a) -> squash (p0 x <==> p1 x))
  : squash ((exists (x : a) . p0 x) <==> (exists (x : a) . p1 x))
  = FStar.Classical.forall_intro_squash_gtot prf

let impl_morph_iff (p0 q0 p1 q1 : Type0)
    (_ : squash (p0 <==> p1))
    (eq_q : squash (p0 /\ p1) -> squash (q0 <==> q1))
  : squash ((p0 ==> q0) <==> (p1 ==> q1))
  = FStar.Classical.Sugar.implies_intro _ _ eq_q

let iff_morph_iff (p0 q0 p1 q1 : Type0)
    (_ : squash (p0 <==> p1))
    (_ : squash (q0 <==> q1))
  : squash ((p0 <==> q0) <==> (p1 <==> q1))
  = ()

let rew_forall_unit' (p0 : U.unit' -> Type) (p1 : Type)
    (_ : squash (p0 U.Unit' <==> p1))
  : squash ((forall (u : U.unit') . p0 u) <==> p1)
  = ()

let rew_exists_unit' (p0 : U.unit' -> Type) (p1 : Type)
    (_ : squash (p0 U.Unit' <==> p1))
  : squash ((exists (u : U.unit') . p0 u) <==> p1)
  = ()

let rew_forall_eq (#a : Type) (#p : a -> Type0) (x : a)
      (h : squash (forall (x' : a) . x' =!= x ==> p x'))
  : squash ((forall x' . p x') <==> p x)
  = ()

let rew_exists_eq (#a : Type) (#p : a -> Type0) (x : a)
      (h : squash (forall (x' : a) . p x' ==> x' == x))
  : squash ((exists x' . p x') <==> p x)
  = ()

let rm_squash p p'
    (_ : squash (p <==> p'))
  : squash (squash p <==> p')
  = ()


/// Used to rewrite a [prop] to an equivalent ([<==>]) one.
/// Solves a goal of the form [p <==> ?p']
// TODO: currently, this can backtrack: prevent backtracking / option ?
let rec rew_iff (pre  : (unit -> Tac unit) -> Tac unit) : Tac unit =
  let r () = rew_iff pre in
  first [
    (fun () -> pre r);
    (fun () -> apply (`conj_morph_iff); iseq [r; (fun () -> let _ = intro () in r ())]);
    // [rew_forall_unit'] needs to be done before [impl_morph_iff]
    (fun () -> apply (`rew_forall_unit'); r ());
    (fun () -> apply (`rew_exists_unit'); r ());
    (fun () -> apply (`impl_morph_iff); iseq [r; (fun () -> let _ = intro () in r ())]);
    (fun () -> apply (`forall_morph_iff); let _ = intro () in r ());
    (fun () -> apply (`exists_morph_iff); let _ = intro () in r ());
    (fun () -> apply (`iff_morph_iff); iseq [r; r]);
    (fun () -> apply (`iff_refl))
  ]

let rec process_hyps (ts : list (term -> Tac (list term))) (hs : list term) : Tac (list term)
  = match hs with
    | [] -> []
    | h0 :: hs -> try first (map (fun (t : term -> Tac (list term)) () ->
                               let hs0 = t h0 in process_hyps ts L.(hs0 @ hs)) ts)
                with | _ -> h0 :: process_hyps ts hs
