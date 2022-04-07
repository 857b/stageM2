module Learn.Steel

module U32 = FStar.UInt32

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

(* ~ Composition SteelBase and Tot
   ? function without side effect
 *)
let eq_test (#a : eqtype) (r1 r2 : ref a) : Steel bool
  (vptr r1 `star` vptr r2) (fun _ -> vptr r1 `star` vptr r2)
  (requires fun _ -> True) (ensures fun h0 b _ -> b = (sel r1 h0 = sel r2 h0))
  = let x1 = read r1 in
    let x2 = read r2 in
    x1 = x2

let alias_test (r1 r2 : ref U32.t) : Steel unit
  (vptr r1 `star` vptr r2) (fun _ -> vptr r1 `star` vptr r2)
  (requires fun _ -> True) (ensures fun _ () h1 -> sel r1 h1 = 1ul /\ sel r2 h1 = 2ul)
  = write r1 1ul;
    write r2 2ul

let alloc_test () : Steel unit emp (fun () -> emp) (fun _ -> True) (fun _ () _ -> True)
  =
    let r = malloc #U32.t 0ul in
    let x = read r in
    (**) assert (x = 0ul);
    write r 1ul;
    let x = read r in
    (**) assert (x == 1ul);
    free r
