module Learn.LowStar.Loops


module U   = Learn.Util
module HS  = FStar.HyperStack
module U32 = FStar.UInt32
module ST  = FStar.HyperStack.ST
open FStar.HyperStack.ST


(* [reverse_for] *)
(* implementation of [C.Loops.reverse_for] using [C.Loops.for] for the extraction *)

noextract inline_for_extraction
let reverse_for (start:U32.t) (finish:U32.t{U32.v finish <= U32.v start})
    (inv:HS.mem -> nat -> Type0)
    (f:(i:U32.t{U32.(v start >= v i /\ v i > v finish)}) -> Stack unit
                        (requires fun h         -> inv h (U32.v i))
                        (ensures  fun h_1 _ h_2 -> U32.(inv h_1 (v i) /\ inv h_2 (v i - 1))) )
  : Stack unit
    (requires fun h       -> inv h (U32.v start))
    (ensures  fun _ _ h_2 -> inv h_2 (U32.v finish))
  = C.Loops.for 0ul U32.(start -^ finish)
                (fun h i -> i <= U32.(v start - v finish) /\ inv h (U32.v start - i))
                (fun i -> f U32.(start -^ i))
  

(* [tail_rec_post h1 post1 post0] expresses the fact that a tail-recursive call (in the exit state [h1] of the
   current step) establish (with its post-condition [post1]) the post-condition [post0] of the current step. *)

let tail_rec_post (#a : Type) (h1 : HS.mem)
  (post1 : a -> HS.mem -> GTot prop) (post0 : a -> HS.mem -> GTot prop)
  : Tot prop
  = U.hide_prop (forall x h2. post1 x h2 /\ equal_stack_domains h1 h2 ==> post0 x h2)

let tail_rec_postI (#a : Type) (h1 : HS.mem)
  (post1 : a -> HS.mem -> GTot prop) (post0 : a -> HS.mem -> GTot prop)
  (pf : (x:a) -> (h2:HS.mem) -> Lemma (requires post1 x h2 /\ equal_stack_domains h1 h2) (ensures post0 x h2))
  : Lemma (ensures tail_rec_post #a h1 post1 post0)
  = U.hide_propI_by (forall x h2. post1 x h2 /\ equal_stack_domains h1 h2 ==> post0 x h2) (fun () ->
       introduce forall x h2. post1 x h2 /\ equal_stack_domains h1 h2 ==> post0 x h2
            with introduce _ ==> _
            with pf0. pf x h2
    )

let tail_rec_postD #a h1 post1 post0 x h2
  : Lemma (requires tail_rec_post #a h1 post1 post0)
          (ensures post1 x h2 /\ equal_stack_domains h1 h2 ==> post0 x h2)
  = U.hide_propD (forall x h2. post1 x h2 /\ equal_stack_domains h1 h2 ==> post0 x h2)

(* [rec_reverse_for] *)

(* [i] is the first parameter of [pre]&[post] to be directly used with [tail_rec_post] *)

noextract inline_for_extraction
let rec_reverse_for_st (start : U32.t) (finish : U32.t{U32.(v finish <= v start)}) (#a : Type)
    (pre  : (i:nat{U32.(v start >= i /\ i >= v finish)}) -> HS.mem -> GTot prop)
    (post : (i:nat{U32.(v start >= i /\ i >= v finish)}) -> (h0:HS.mem) -> a -> HS.mem ->
            Ghost prop (requires pre i h0) (ensures fun _ -> True))
    (body : (i:U32.t{U32.(v start >= v i /\ v i > v finish)}) -> Stack unit
              (requires fun h0       -> pre (U32.v i) h0)
              (ensures  fun h0 () h1 -> pre (U32.v i - 1) h1 /\
                           tail_rec_post h1 (post (U32.v i - 1) h1) (post (U32.v i) h0)))
    (exit : unit -> ST a
              (requires fun h0      -> pre  (U32.v finish) h0)
              (ensures  fun h0 x h1 -> post (U32.v finish) h0 x h1))
  : ST a (requires fun h0      -> pre  (U32.v start) h0)
         (ensures  fun h0 x h1 -> post (U32.v start) h0 x h1)
  =
    let h0 = ST.get () in
    let inv_p = fun h1 (i : nat) ->
                U32.(v start >= i /\ i >= v finish) /\
                pre i h1 /\
               (forall x h2 . post i h1 x h2 /\ equal_stack_domains h1 h2 ==> post (U32.v start) h0 x h2)
    in let inv = fun (h1 : HS.mem) (i : nat) -> U.hide_prop (inv_p h1 i)
    in let body'
      : (i:U32.t{U32.(v start >= v i /\ v i > v finish)}) -> Stack unit
                    (requires fun h -> inv h (U32.v i))
                    (ensures fun h0 () h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i - 1))
            = fun i ->
                  let vi = U32.v i in
                  let h1 = ST.get () in
                  U.hide_propD (inv_p h1 vi);
                  body i;
                  let h2 = ST.get () in
                  assert_norm (
                      tail_rec_post h2 (post (vi - 1) h2) (post vi h1) ==
                      U.hide_prop (forall x h3 . post (vi - 1) h2 x h3 /\ equal_stack_domains h2 h3 ==> post vi h1 x h3));
                  U.hide_propD (forall x h3 . post (vi - 1) h2 x h3 /\ equal_stack_domains h2 h3 ==> post vi h1 x h3);
                  U.hide_propI (inv_p h2 (vi - 1))
    in
    U.hide_propI (inv_p h0 (U32.v start));
    let h00 = ST.get () in
    U.prop_equal (fun h -> inv h (U32.v start)) h0 h00;
    reverse_for start finish inv body';
    let h1 = ST.get () in
    assert (inv h1 (U32.v finish));
    U.assert_by (pre (U32.v finish) h1)
              (fun () -> U.hide_propD (inv_p h1 (U32.v finish)));
    let rt = exit () in
    let h2 = ST.get () in
    U.assert_by (post (U32.v start) h0 rt h2)
              (fun () -> U.hide_propD (inv_p h1 (U32.v finish)));
    rt


(* [rec_while] *)

(* We require that [test] does not modify the state ([h0' == h0]) because [body]&[exit] need to refer to [h0].
   We could allow [h0' =!= h0] if we had a way to store [h0] (without modifying the state) in order to give it
   to [body]&[exit]. Anyway, the extraction seems to remove any expression with side-effects from the guard (by
   duplicating it). *)
noextract inline_for_extraction
let rec_while_st (#a : Type)
    (pre       : HS.mem -> GTot prop)
    (post_test : (h0:HS.mem) -> bool ->
                   Ghost prop (requires pre h0) (ensures fun _ -> True))
    (post      : (h0:HS.mem) -> a -> HS.mem ->
                   Ghost prop (requires pre h0) (ensures fun _ -> True))
    (test : unit -> Stack bool
              (requires fun h0       -> pre h0)
              (ensures  fun h0 b h0' -> h0' == h0 /\
                                     post_test h0 b))
    (body : unit -> Stack unit
              (requires fun h0       -> pre h0 /\ post_test h0 true)
              (ensures  fun h0 () h1 -> pre h1 /\
                                     tail_rec_post h1 (post h1) (post h0)))
    (exit : unit -> ST a
              (requires fun h0       -> pre h0 /\ post_test h0 false)
              (ensures  fun h0 x h1  -> post h0 x h1))
  : ST a (requires fun h0      -> pre  h0)
         (ensures  fun h0 x h1 -> post h0 x h1)
  =
    let h0 = ST.get () in
    let test_pre h1 =
      pre h1 /\
      (forall x h2 . post h1 x h2 /\ equal_stack_domains h1 h2 ==> post h0 x h2)
    in let test_post b h1 =
      test_pre h1 /\
      post_test h1 b
    in
    let test' () : Stack bool
              (requires fun h1      -> test_pre h1)
              (ensures  fun _ b h1' -> test_post b h1')
      = test ()
    in
    let body' () : Stack unit
              (requires fun h1      -> test_post true h1)
              (ensures  fun _ () h2 -> test_pre h2)
      =   let h1 = ST.get () in
        body ();
          let h2 = ST.get () in
          introduce forall x h3 . post h2 x h3 /\ equal_stack_domains h2 h3 ==> post h0 x h3
            with begin
                 eliminate forall x h3 . post h1 x h3 /\ equal_stack_domains h1 h3 ==> post h0 x h3
                      with x h3;
                 tail_rec_postD h2 (post h2) (post h1) x h3
            end
    in
    C.Loops.while #test_pre #test_post test' body';
    exit ()


noextract inline_for_extraction
let rec_while (#a : Type)
    (pre       : HS.mem -> GTot prop)
    (post_test : (h0:HS.mem) -> bool ->
                   Ghost prop (requires pre h0) (ensures fun _ -> True))
    (post      : (h0:HS.mem) -> a -> HS.mem ->
                   Ghost prop (requires pre h0) (ensures fun _ -> True))
    (test : unit -> Stack bool
              (requires fun h0       -> pre h0)
              (ensures  fun h0 b h0' -> h0' == h0 /\
                                     post_test h0 b))
    (body : unit -> Stack unit
              (requires fun h0       -> pre h0 /\ post_test h0 true)
              (ensures  fun h0 () h1 -> pre h1 /\
                                     tail_rec_post h1 (post h1) (post h0)))
    (exit : unit -> Stack a
              (requires fun h0       -> pre h0 /\ post_test h0 false)
              (ensures  fun h0 x h1  -> post h0 x h1))
  : Stack a (requires fun h0      -> pre  h0)
            (ensures  fun h0 x h1 -> post h0 x h1)
  =
    let post' h0 x h1 : Ghost prop (requires pre h0) (ensures fun _ -> True) =
        post h0 x h1 /\ ST.equal_domains h0 h1 in
    rec_while_st pre post_test post'
                 test
                 (fun () ->
                   let h0 = ST.get () in
                   body ();
                   let h1 = ST.get () in
                   tail_rec_postI h1 (post' h1) (post' h0) (fun x h2 ->
                     tail_rec_postD h1 (post h1) (post h0) x h2))
                 exit
