module Learn.Steel.QueueP.Test

module L = FStar.List.Pure
module G = FStar.Ghost

open Steel.Effect
open Steel.Effect.Atomic
open Steel.Reference

open Learn.Steel.QueueP
open Learn.Steel.ListP.Test


let p0_queue_t = ref (queue_st cell0)

let p0_malloc   = malloc p0
let p0_free     = free p0
let p0_is_empty = is_empty p0
let p0_enqueue  = enqueue p0
let p0_dequeue  = dequeue p0


let test_p0 () : SteelT unit emp (fun () -> emp)
  =
    let q = p0_malloc () in
    let x0 = Steel.Reference.malloc #cell0 ({next = null; data_x = 0ul; data_y = true}) in
    p0_enqueue x0 q;
    (**) let x0_c : cell_t p0 = (|x0, (0ul, true)|) in
    (**) assert_norm (L.snoc ([], x0_c) == [x0_c]);
    let x1 = Steel.Reference.malloc #cell0 ({next = null; data_x = 1ul; data_y = false}) in
    p0_enqueue x1 q;
    let x0' = p0_dequeue q in
    (**) assert (x0' == x0);
    let x0_v = read x0' in
    (**) assert (x0_v.data_x = 0ul /\ x0_v.data_y = true);
    write x0' ({x0_v with data_x = 2ul});
    p0_enqueue x0' q;
    let x1' = p0_dequeue q in
    (**) assert (x1' == x1);
    let x0' = p0_dequeue q in
    (**) assert (x0' == x0);
    Steel.Reference.free x0';
    Steel.Reference.free x1';
    p0_free q
