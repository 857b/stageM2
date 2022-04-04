module Learn.Tactics.Test

module T   = FStar.Tactics
module Tuq = Learn.Tactics.Unsquash

open FStar.Calc
open FStar.List.Pure

(*
[@expect_failure]
let () = assert ((True ==> False) ==> (forall (x : nat) . False))
           by Tuq.(let h = impI () in
                   let x = allI () in T.revert ();
                   let _ = impD h in
                   T.qed ())

[@expect_failure]
let () = assert ((True /\ False) ==> (forall (x : nat) . False))
           by Tuq.(let h = impI () in
                   let x = allI () in T.revert ();
                   let _ = andD h in
                   T.qed ())

[@expect_failure]
let () = assert ((forall (x y:nat) . False) ==> (forall (x : nat) . True))
           by Tuq.(let _ = hyp_arrow_morph_right (fun x p -> allD p) (allD (impI ())) in
                   T.qed ())

[@expect_failure]
let () = assert ((True ==> False) /\ (forall (x : int) . True))
           by Tuq.(andI1 ();
                   goal_pair_morph (fun () -> let _ = impI() in T.revert ())
                                   (fun () -> let _ = allI() in T.revert ());
                   T.qed ())

[@expect_failure]
let () = assert (((True ==> False) /\ (forall (x:int) . True)) ==> False)
           by Tuq.(let h = andD1 (impI ()) in
                   let _ = hyp_pair_morph impD allD h in
                   T.qed ())
*)

let test0 (a : Type) (f : a -> prop) (hd : a) (tl : list a) =
  assert (f hd /\ (forall (i:nat{i < length tl}). f (index tl i))
            ==> (forall (i:nat{i < length (hd :: tl)}) . f (index (hd :: tl) i)))
      by (Tuq.(usq true true (Imp (And Nop (All Nop)) (All Nop)));
          Tuq.lbd_exact (`(fun h_hd h_tl i -> if i = 0 then h_hd else h_tl (i-1))))

let test1 (a : Type) (f : a -> prop) (hd : a) (tl : list a) =
  assert (f hd /\ (forall (i:nat{i < length tl}). f (index tl i))
           <==> (forall (i:nat{i < length (hd :: tl)}) . f (index (hd :: tl) i)))
      by (Tuq.(lbd_prfs (`(_ /\ (forall i._) <==> (forall i._))))
              [(`(fun h_hd h_tl i -> if i = 0 then h_hd else h_tl (i-1)));
               (`(fun hi -> hi 0));
               (`(fun hi i -> hi (i+1)))])

let test2 (a : Type) (p : a -> a -> prop) =
  assert ((forall (x y : a) . p x y) ==> (forall (x y : a) . p y x))
    by (Tuq.(lbd_prf (`((forall x y._) ==> (forall x y._))))
            (`(fun h x y -> h y x)))

let test3 (p : nat -> prop) =
  assert ((forall (i:nat) . p i) ==> p 0 /\ p 1)
    by (Tuq.(usq false true (Imp (All Nop) (And Nop Nop)));
        Tuq.lbd_exact (`(fun h -> (h 0, h 1))))

let test4 (p q : nat -> prop) =
  assert ((forall (i:nat) . p i /\ (p (i+1) ==> q i)) ==> p 0 /\ q 0)
    by (Tuq.(lbd_prf (`((forall i._ /\ (_==>_)) ==> _ /\ _)))
            (`(fun h -> (h 0)._1, (h 0)._2 (h 1)._1)))

let test5 (p q : prop) =
  assert (p /\ (p ==> q) ==> p /\ q)
    by (Tuq.(lbd_prf (`(_ /\ (_ ==> _) ==> _ /\ _)))
            (`(fun hp hq -> (hp, hq hp))))

(*
[@expect_failure 228] (* [tl] not found *)
let test6 (a : Type) (f : a -> prop) (hd : a) (tl : list a) =
   assert ((forall (i:nat{i < length (hd :: tl)}) . f (index (hd :: tl) i))
           ==> f hd /\ (forall (i:nat{i < length tl}). f (index tl i)))
      by (Tuq.(lbd_prf (`((forall i._) ==> _ /\ (forall i._))))
              (`(fun h -> (h 0, (fun (i: nat{i < length tl}) -> h (i + 1))))))
*)

(* ASSERTION FAILURE 
let test6' (a : Type) (f : a -> prop) (hd : a) (tl : list a) =
   assert ((forall (i:nat{i < length (hd :: tl)}) . f (index (hd :: tl) i))
           ==> f hd /\ (forall (i:nat{i < length tl}). f (index tl i)))
      by (Tuq.(lbd_prf (`((forall i._) ==> _ /\ (forall i._))))
              (quote (fun h -> (h 0, (fun (i: nat{b2t(i < length tl)}) -> h (i + 1))))))
 *)

let test7 (f : nat -> prop) (i : nat) =
  assert ((forall (j:nat) . f j) ==> f i)
    by (T.revert ();
        let i  = T.intro () in
        let h  = T.implies_intro () in
        let h' = T.instantiate h i in
        T.hyp h')

let test8 (p q r : prop) =
  assert (p ==> (p ==> q /\ r) ==> r)
    by (Tuq.(lbd_prf (`(_ ==> (_ ==> _ /\ _) ==> _)))
            (`(fun hp hqr  -> (hqr hp)._2)))

(*
[@expect_failure]
let test9 (a : Type) (l : list a) : unit
  = match l with
    | [] -> ()
    | hd :: tl ->
        assert (l == hd :: tl); (* OK *)
        assert (l == hd :: tl)
          by T.(dump "test9.1"; smt (); qed ()); (* OK *)
        calc (==) {
            l;
          == {assert (l == hd :: tl)} (* OK *)
            hd :: tl;
        };
        calc (==) {
            l;
          == {_ by T.(dump "test9.2"; smt (); qed ())} (* KO *)
            hd :: tl;
        }
*)
