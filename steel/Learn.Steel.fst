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


(* -------------------------- *)

inline_for_extraction noextract noeq
type aptr_p' (t : Type) = {
  a  : Type;
  vp : a -> vprop;
  of_sel  : (r:a) -> normal (t_of (vp r)) -> GTot t;
  set_sel : (r:a) -> normal (t_of (vp r)) -> (x : t) ->
            Ghost (normal (t_of (vp r))) (requires True) (ensures fun rt -> of_sel r rt == x);
  read  : (r:a) -> Steel t (vp r) (fun _ -> vp r) (requires fun _ -> True)
                     (ensures fun h0 x h1 -> frame_equalities (vp r) h0 h1 /\ x == of_sel r (h0 (vp r)));
  write : (r:a) -> (x : t) -> Steel unit (vp r) (fun _ -> vp r) (requires fun _ -> True)
                     (ensures fun h0 () h1 -> h1 (vp r) == set_sel r (h0 (vp r)) x)
}

inline_for_extraction noextract
type aptr_p (t : Type) = p:aptr_p' t {
     forall (r:p.a) (s : normal (t_of (p.vp r))) (x0 x1 : t) . {:pattern (p.set_sel r (p.set_sel r s x0) x1)}
       p.set_sel r (p.set_sel r s x0) x1 == p.set_sel r s x1
  }  (* TODO [set_sel s (of_sel s) == s] *)


inline_for_extraction noextract noeq
type get_set_t' (c t : Type) = {
  get : c -> Tot t;
  set : c -> t -> Tot c;
}

inline_for_extraction noextract
type get_set_t (c t : Type) = p:get_set_t' c t {
     (forall (s : c) (x : t) . {:pattern (p.get (p.set s x))}
        p.get (p.set s x) == x) /\
     (forall (s : c) (x0 x1 : t) . {:pattern (p.set (p.set s x0) x1)}
        p.set (p.set s x0) x1 == p.set s x1)
  }

inline_for_extraction noextract
let aptr_of_vptr (#t : Type) : Tot (aptr_p t) = {
  a       = ref t;
  vp      = vptr;
  of_sel  = (fun r x   -> (x <: t));
  set_sel = (fun r _ x -> x);
  read    = (fun r   -> read r);
  write   = (fun r x -> write r x)
}

inline_for_extraction noextract
let aptr_of_get_set (#c #t : Type) ($p : get_set_t c t) : Tot (aptr_p t) = {
  a       = ref c;
  vp      = vptr;
  of_sel  = (fun r x   -> p.get x);
  set_sel = (fun r s x -> p.set s x);
  read    = (fun r   -> let s = read r in p.get s);
  write   = (fun r x -> let s = read r in write r (p.set s x))
}


inline_for_extraction noextract
let test_set_ptr (xp yp : aptr_p U32.t) (x : xp.a) (y : yp.a)
  : Steel unit (xp.vp x `star` yp.vp y) (fun () -> xp.vp x `star` yp.vp y)
               (requires fun _ -> True)
               (ensures fun h0 () h1 -> h1 (xp.vp x) == h0 (xp.vp x) /\
                                     h1 (yp.vp y) == yp.set_sel y (h0 (yp.vp y)) (xp.of_sel x (h0 (xp.vp x))))
  = let v = xp.read x in
    yp.write y v

(*
inline_for_extraction noextract
let rec test_set_ptr_rec (i : U32.t) (x y : aptr_t U32.t)
  : Steel unit (x.vp `star` y.vp) (fun () -> x.vp `star` y.vp)
               (requires fun _ -> True)
               (ensures fun h0 () h1 -> h1 x.vp == h0 x.vp /\
                                     h1 y.vp == y.set_sel (h0 y.vp) (x.of_sel (h0 x.vp)))
  = if i = 0ul then begin
      let v = x.read () in
      y.write v
    end else
      test_set_ptr_rec U32.(i -^ 1ul) x y
*)

type test_struct = {
  fld_a : U32.t;
  fld_b : bool
}

inline_for_extraction noextract
let test_struct_gs_fld_a : get_set_t test_struct U32.t = {
  get = (fun c -> c.fld_a);
  set = (fun c x -> {c with fld_a = x})
}

let test_set_ptr_caller () : SteelT unit emp (fun () -> emp)
  =
    let x  = malloc #U32.t 42ul in
    let ys = malloc #test_struct ({fld_a = 0ul; fld_b = false}) in
    test_set_ptr aptr_of_vptr (aptr_of_get_set test_struct_gs_fld_a) x ys;
    let i = read x in
      assert (i == 42ul);
    let i = read ys in
      assert (i == {fld_a = 42ul; fld_b = false});
    free x;
    free ys
