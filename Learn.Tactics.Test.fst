module Learn.Tactics.Test

module T   = FStar.Tactics
module Tuq = Learn.Tactics.Unsquash

open FStar.List.Pure
open Learn.List


[@expect_failure]
let () = assert ((True ==> False) ==> (forall (x : nat) . False))
             by (let h = impI () in
                 let x = allI () in revert ();
                 let _ = impD h in
                 qed ())

[@expect_failure]
let () = assert ((True /\ False) ==> (forall (x : nat) . False))
             by (let h = impI () in
                 let x = allI () in revert ();
                 let _ = andD h in
                 qed ())

let test0 (a : Type) (f : a -> prop) (hd : a) (tl : list a) : unit =
  assert (f hd /\ (forall (i:nat{i < length tl}). f (index tl i))
            ==> (forall (i:nat{i < length (hd :: tl)}) . f (index (hd :: tl) i)))
      by (Tuq.(usq (Imp (And Nop (All Nop)) (All Nop)));
          Tuq.lbd_exact (`(fun h_hd h_tl i -> if i = 0 then h_hd else h_tl (i-1))))

let test1 (a : Type) (f : a -> prop) (hd : a) (tl : list a) : unit =
  assert (f hd /\ (forall (i:nat{i < length tl}). f (index tl i))
           <==> (forall (i:nat{i < length (hd :: tl)}) . f (index (hd :: tl) i)))
      by (Tuq.(lbd_prf (iff (And Nop (All Nop)) (All Nop)))
              [(`(fun h_hd h_tl i -> if i = 0 then h_hd else h_tl (i-1)));
               (`(fun hi -> hi 0));
               (`(fun hi i -> hi (i+1)))])
  
