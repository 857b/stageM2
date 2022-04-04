module Learn.LowStar.Queue.Param

module Ll  = Learn.List
module B   = LowStar.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack

(* [c] : type of cells *)

type cell_ptr (c : Type) = B.pointer_or_null c

type cell_list (c : Type) = list (B.pointer c)

noeq type queue_param (c : Type) = {
  get_next : c -> cell_ptr c;
  set_next : c -> cell_ptr c -> c;
  mod_next : c -> c -> prop;
  get_set_next : (x : c) -> (y : cell_ptr c) ->
                 Lemma (get_next (set_next x y) == y);
  set_set_next : (x : c) -> (y0 : cell_ptr c) -> (y1 : cell_ptr c) ->
                 Lemma (set_next (set_next x y0) y1 == set_next x y1);
  mod_refl     : (x : c) ->
                 Lemma (mod_next x x);
  (* TODO? mod_trans *)
  mod_set_next : (x : c) -> (y : cell_ptr c) ->
                 Lemma (mod_next x (set_next x y))
}


let open_queue_param (#c : Type) (a : queue_param c)
  : Lemma (ensures
      (forall (x : c) (y : cell_ptr c) . {:pattern (a.get_next (a.set_next x y))}
           a.get_next (a.set_next x y) == y) /\
      (forall (x : c) (y0 y1 : cell_ptr c) . {:pattern (a.set_next (a.set_next x y0) y1)}
           a.set_next (a.set_next x y0) y1 == a.set_next x y1) /\
      (forall (x : c) . {:pattern (a.mod_next x x)}
           a.mod_next x x) /\
      (forall (x : c) (y : cell_ptr c) . {:pattern (a.mod_next x (a.set_next x y))}
           a.mod_next x (a.set_next x y))
    )
  =
    introduce forall (x : c) (y : cell_ptr c) . a.get_next (a.set_next x y) == y
         with a.get_set_next x y;
    introduce forall (x : c) (y0 y1 : cell_ptr c) . a.set_next (a.set_next x y0) y1 == a.set_next x y1
         with a.set_set_next x y0 y1;
    introduce forall (x : c) . a.mod_next x x
         with a.mod_refl x;
    introduce forall (x : c) (y : cell_ptr c) . a.mod_next x (a.set_next x y)
         with a.mod_set_next x y


let mod_next (#c : Type) (a : queue_param c) (h0 h1 : HS.mem) (x : B.pointer c) : GTot prop
  = B.live h0 x /\ B.live h1 x /\ a.mod_next (B.deref h0 x) (B.deref h1 x)

let mod_next_list (#c : Type) (a : queue_param c) (h0 h1 : HS.mem) (xs : cell_list c)
  : GTot prop
  = Ll.g_for_allP xs (mod_next a h0 h1)

let mod_data (#c : Type) (a : queue_param c) (h0 h1 : HS.mem) (x : B.pointer c) : GTot prop
  = B.live h0 x /\ B.live h1 x /\ a.get_next (B.deref h0 x) == a.get_next (B.deref h1 x)

let mod_data_list (#c : Type) (a : queue_param c) (h0 h1 : HS.mem) (xs : cell_list c)
  : GTot prop
  = Ll.g_for_allP xs (mod_data a h0 h1)


let disjoint_mod_next (#c : Type) (a : queue_param c) (h0 h1 : HS.mem) (p : M.loc) (x : B.pointer c)
  : Lemma (requires M.(loc_disjoint (loc_buffer x) p /\ live h0 x /\ modifies p h0 h1))
          (ensures  mod_next a h0 h1 x)
          [SMTPat M.(modifies p h0 h1); SMTPat (mod_next a h0 h1 x)]
  = a.mod_refl (B.deref h0 x)
