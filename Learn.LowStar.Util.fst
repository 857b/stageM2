module Learn.LowStar.Util

module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module U32 = FStar.UInt32

(* necessary for hint replay *)
noextract inline_for_extraction
let u32_zero : x: U32.t {U32.v x == 0}
  = U32.uint_to_t 0

(* force a proof of [M.modifies] by transitivity *)
#push-options "--ifuel 1"
noextract noeq type mod_seq (#mod : M.loc) : HS.mem -> HS.mem -> Type =
  | MNil  : h : HS.mem -> mod_seq #mod h h
  | MCons : h0 : HS.mem -> #h1 : HS.mem -> #h2 : HS.mem ->
               #squash (M.modifies mod h0 h1) -> mod_seq #mod h1 h2 -> mod_seq #mod h0 h2

let rec mod_of_seq (mod : M.loc) (#h0 #h1 : HS.mem) (sq : mod_seq #mod h0 h1)
  : Lemma (ensures M.modifies mod h0 h1) (decreases sq)
  = match sq with
    | MNil _ -> ()
    | MCons _ sq -> mod_of_seq mod sq
#pop-options
