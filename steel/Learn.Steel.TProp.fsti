module Learn.Steel.TProp

module Mem = Steel.Memory
open FStar.Ghost
open Steel.Memory
open Steel.Effect.Atomic


(*** [tprop] *)

[@@ erasable]
noeq
type tprop (t : Type0) = {
  t_hp  : slprop u#1;
  t_sel : selector t t_hp;
}

let tprop_of_vprop (t : Type) (v : vprop {normal (t_of v) == t}) : tprop t = {
  t_hp  = hp_of v;
  t_sel = sel_of v;
}

let vprop'_of_tprop (#t : Type) (u : tprop t) : vprop' = {
  hp  = u.t_hp;
  t;
  sel = u.t_sel
}

let vprop_of_tprop (#t : Type) (u : tprop t) : vprop
  = VUnit (vprop'_of_tprop u)


(***** [tprop_interp] *)

/// We use [option slprop] to avoid introducing some [Mem.emp] in the [slprop].

let slprop_of_opt (slp : option slprop) : slprop
  = match slp with
  | Some slp -> slp
  | None     -> Mem.emp

let interp_opt (slp : option slprop) (m : mem) : prop
  = match slp with
  | Some slp -> interp slp m
  | None     -> True

val interp_of_opt (slp : option slprop) (m : mem)
  : Lemma (interp_opt slp m <==> interp (slprop_of_opt slp) m)

let star_opt (slp0 slp1 : option slprop) : option slprop
  = match slp0 with
    | None      -> slp1
    | Some slp0 ->
    match slp1 with
    | None      -> Some slp0
    | Some slp1 -> Some (slp0 `Mem.star` slp1)

val star_of_opt (slp0 slp1 : option slprop)
  : Lemma (slprop_of_opt (star_opt slp0 slp1) `Mem.equiv` (slprop_of_opt slp0 `Mem.star` slprop_of_opt slp1))

val interp_star_opt (slp0 slp1 : option slprop) (m : mem)
  : Lemma (interp_opt (star_opt slp0 slp1) m <==>
            (exists (m0 m1 : mem) . disjoint m0 m1 /\ join m0 m1 == m /\ interp_opt slp0 m0 /\ interp_opt slp1 m1))


type tprop_interp
       (#t : Type) (u : tprop t)
       (guard : (m : mem) -> prop)
       (req   : (m : mem {guard m}) -> Type0)
       (slp   : (m : mem {guard m /\ req m}) -> GTot (option slprop))
       (sel   : (m : mem {guard m /\ req m}) -> GTot t)
  = {
    tpi_int_sl : squash (forall (m : mem {guard m}) . (interp u.t_hp m <==> req m /\ interp_opt (slp m) m));
    tpi_sel_eq : squash (forall (m : Mem.hmem u.t_hp {guard m /\ req m}) . u.t_sel m == sel m);
    tpi_join0  : squash (forall (m0: mem{guard m0 /\ req m0}) (m1:mem{disjoint m0 m1}) .
                           guard (join m0 m1) /\ req (join m0 m1) /\
                           slp (join m0 m1) == slp m0 /\ sel (join m0 m1) == sel m0);
    tpi_join1  : squash (forall (m0:mem) (m1:mem{disjoint m0 m1}) .
                           (guard (join m0 m1) /\ req (join m0 m1) /\
                             (interp u.t_hp m0 \/ interp_opt (slp (join m0 m1)) m0)) ==>
                           (guard m0 /\ req m0))
  }

val tprop_interp_intro
      (#t : Type) (u : tprop t)
      (guard : (m : mem) -> prop)
      (req   : (m : mem {guard m}) -> Type0)
      (slp   : (m : mem {guard m /\ req m}) -> GTot (option slprop))
      (sel   : (m : mem {guard m /\ req m}) -> GTot t)
      (int_sl : (m : mem) -> squash (guard m) ->
                squash (interp u.t_hp m <==> req m /\ interp_opt (slp m) m))
      (sel_eq : (m : Mem.hmem u.t_hp) -> squash (guard m /\ req m /\ interp_opt (slp m) m) ->
                squash (u.t_sel m == sel m))
      (join0  : (m0:mem{guard m0 /\ req m0}) -> (m1:mem{disjoint m0 m1}) ->
                   squash (let m = join m0 m1 in guard m /\ req m /\ slp m == slp m0 /\ sel m == sel m0))
      (join1  : (m0:mem) -> (m1:mem{disjoint m0 m1}) ->
                   squash (let m = join m0 m1 in guard m /\ req m /\ (interp u.t_hp m0 \/ interp_opt (slp m) m0)) ->
                   squash (guard m0 /\ req m0))
  : tprop_interp u guard req slp sel

val tprop_interp_elim
      (#t : Type) (#u : tprop t)
      (#guard : (m : mem) -> prop)
      (#req   : (m : mem {guard m}) -> Type0)
      (#slp   : (m : mem {guard m /\ req m}) -> GTot (option slprop))
      (#sel   : (m : mem {guard m /\ req m}) -> GTot t)
      (tpi    : tprop_interp u guard req slp sel)
      (m : mem)
  : Lemma (requires guard m)
          (ensures (interp u.t_hp m <==> (req m /\ interp_opt (slp m) m)) /\
                   (interp u.t_hp m ==> u.t_sel m == sel m))


val tprop_trivial_interp (#t : Type) (u : tprop t)
  : tprop_interp u (fun _ -> True) (interp (u.t_hp)) (fun _ -> Some u.t_hp) (u.t_sel)

val tprop_of_vprop_interp (t : Type) (v : vprop {normal (t_of v) == t})
  : tprop_interp (tprop_of_vprop t v) (fun _ -> True) (interp (hp_of v)) (fun _ -> Some (hp_of v)) (sel_of v)


(*** Combinators *)

// similar to the library of examples/steel/CQueue

(***** [treturn] *)

val treturn (#a : Type) (x : erased a) : tprop a

val treturn_int_sl (#a : Type) (x : erased a) (m : mem)
  : Lemma (interp (treturn x).t_hp m)

val treturn_sel_eq (#a : Type) (x : erased a) (m : mem)
  : Lemma (treturn_int_sl x m;
           (treturn x).t_sel m == reveal x)

val treturn_interp (#a : Type) (x : erased a)
  : tprop_interp (treturn x) (fun _ -> True) (fun _ -> True) (fun _ -> None) (fun _ -> x)

(***** [tbind] *)

val tbind (#a #b : Type) (u : tprop a) (v : a -> tprop b) : tprop b

val tbind_int_sl (#a #b : Type) (u : tprop a) (v : a -> tprop b) (m : mem)
  : Lemma (interp (tbind u v).t_hp m <==>
            (interp u.t_hp m /\ interp (u.t_hp `Mem.star` (v (u.t_sel m)).t_hp) m))

val tbind_sel_eq (#a #b : Type) (u : tprop a) (v : a -> tprop b) (m : Mem.hmem (tbind u v).t_hp)
  : Lemma (tbind_int_sl u v m;
           (tbind u v).t_sel m == (v (u.t_sel m)).t_sel m)

val tbind_interp
      (#a #b : Type) (u : tprop a) (v : a -> tprop b)

      (#u_guard : (m : mem) -> prop)
      (#u_req   : (m : mem {u_guard m}) -> Type0)
      (#u_slp   : (m : mem {u_guard m /\ u_req m}) -> GTot (option slprop))
      (#u_sel   : (m : mem {u_guard m /\ u_req m}) -> GTot a)
      (u_tpi    : tprop_interp u u_guard u_req u_slp u_sel)

      (#v_guard : a -> (m : mem) -> prop)
      (#v_req   : (x: a) -> (m : mem {v_guard x m}) -> Type0)
      (#v_slp   : (x: a) -> (m : mem {v_guard x m /\ v_req x m}) -> GTot (option slprop))
      (#v_sel   : (x: a) -> (m : mem {v_guard x m /\ v_req x m}) -> GTot b)
      (v_tpi    : (x: a) -> tprop_interp (v x) (v_guard x) (v_req x) (v_slp x) (v_sel x))

  : tprop_interp (tbind u v)
      (fun m -> u_guard m /\ (u_req m ==> v_guard (u_sel m) m))
      (fun m -> u_req m /\ v_req (u_sel m) m)
      (fun m -> u_slp m `star_opt` v_slp (u_sel m) m)
      (fun m -> v_sel (u_sel m) m)

(***** [tpure] *)

val tpure (p : Type0) : tprop (squash p)

val tpure_int_sl (p : Type0) (m : mem)
  : Lemma (interp (tpure p).t_hp m <==> p)

val tpure_sel_eq (p : Type0) (m : Mem.hmem (tpure p).t_hp)
  : Lemma (tpure_int_sl p m;
           (tpure p).t_sel m == ())

val tpure_interp (p : Type0)
  : tprop_interp (tpure p) (fun _ -> True) (fun _ -> p) (fun _ -> None) (fun _ -> ())

(***** if-then-else *)

// ALT? explore both branches at the same time, remove guard

val ite_interp_then
      (#a : Type) (b : bool) (thn : tprop a) (els : tprop a)
      (#guard : (m : mem) -> prop)
      (#req   : (m : mem {guard m}) -> Type0)
      (#slp   : (m : mem {guard m /\ req m}) -> GTot (option slprop))
      (#sel   : (m : mem {guard m /\ req m}) -> GTot a)
      (tpi    : tprop_interp thn guard req slp sel)
  : tprop_interp (if b then thn else els) (fun m -> b /\ guard m) req slp sel

val ite_interp_else
      (#a : Type) (b : bool) (thn : tprop a) (els : tprop a)
      (#guard : (m : mem) -> prop)
      (#req   : (m : mem {guard m}) -> Type0)
      (#slp   : (m : mem {guard m /\ req m}) -> GTot (option slprop))
      (#sel   : (m : mem {guard m /\ req m}) -> GTot a)
      (tpi    : tprop_interp els guard req slp sel)
  : tprop_interp (if b then thn else els) (fun m -> ~b /\ guard m) req slp sel


(*** Tactic *)

module L = FStar.List.Pure
open FStar.Tactics

irreducible let __norm_tprop__ : unit = ()

/// Solves a goal [tprop_interp #a tp ?guard ?req ?slp ?sel]
let rec build_tprop_interp (branch : list int) : Tac (list int)
  =
    let goal = cur_goal () in
    let _, args = collect_app goal in
    guard (L.length args = 6);
    let tp = (L.index args 1)._1 in
    match inspect tp with
    | Tv_App _ _ ->
        let hd = match inspect (collect_app tp)._1 with
                 | Tv_FVar v | Tv_UInst v _ -> v
                 | _ -> fail "build_tprop_interp"
        in let hd = implode_qn (inspect_fv hd) in
        if hd = `%tprop_of_vprop
        then (apply (`tprop_of_vprop_interp); branch)
        else if hd = `%treturn
        then (apply (`treturn_interp); branch)
        else if hd = `%tbind
        then begin
          apply (`tbind_interp);
          // u_tpi
          let branch = build_tprop_interp branch in
          // v_tpi
          let x = intro () in
          build_tprop_interp branch
        end else if hd = `%tpure
        then (apply (`tpure_interp); branch)
        else fail "build_tprop_interp"
    | Tv_Match _ _ _ -> // must be an if
        begin match branch with
        | 0 :: branch -> apply (`tprop_trivial_interp); branch
        | 1 :: branch -> apply (`ite_interp_then);
                       // We renormalize since the if was blocking the reduction
                       norm [delta_attr [`%__norm_tprop__]];
                       build_tprop_interp branch
        | 2 :: branch -> apply (`ite_interp_else);
                       norm [delta_attr [`%__norm_tprop__]];
                       build_tprop_interp branch
        | i :: branch -> fail ("invalid branch number: "^string_of_int i)
        | []         -> fail "out of branches"
        end
    | _ -> fail "build_tprop_interp"

private
let __pose_interp_lemma
      (#a : Type) (u : tprop a) (m : mem)
      (#guard : (m : mem) -> prop)
      (#req   : (m : mem {guard m}) -> Type0)
      (#slp   : (m : mem {guard m /\ req m}) -> GTot (option slprop))
      (#sel   : (m : mem {guard m /\ req m}) -> GTot a)
      (tpi    : tprop_interp u guard req slp sel)
      (hguard : squash (guard m))
      (#goal  : Type)
      (k      : squash ((interp u.t_hp m <==> req m /\ interp_opt (slp m) m) /\
                        (interp u.t_hp m ==> u.t_sel m == sel m)) ->
                goal)
  : goal
  = tprop_interp_elim tpi m;
    k ()

let pose_interp_lemma
      (u : term) (m : term)
      (rew_u : unit -> Tac unit)
      (branch : list int) : Tac binder
  =
    apply (`__pose_interp_lemma (`#u) (`#m));
    // tpi
    rew_u ();
    norm [delta_attr [`%__norm_tprop__]];
    let branch = build_tprop_interp branch in
    if Cons? branch then fail "remaining branches";
    // hguard
    norm [simplify]; smt ();
    // k
    let h = intro () in
    norm_binder_type [delta_only [`%interp_opt; `%star_opt]; iota; zeta; simplify] h;
    h


(*** Notations *)

/// Warning:
/// The types inferred by F* for [bind] are often different from the types expected by the tactic.
/// This lead to a `could not instantiate error`. When this happen, using [vprt] instead of [vpr] or
/// adding an explicit type annotation on [return] (using the first, implicit, argument) can solve the problem.

[@@__norm_tprop__] let return = treturn
[@@__norm_tprop__] let bind (#a #b : Type) ($u : tprop a) (v : a -> tprop b) = tbind u v
[@@__norm_tprop__] let vprt = tprop_of_vprop
[@@__norm_tprop__] let vpr (v : vprop) = tprop_of_vprop (normal (t_of v)) v
/// [tpr] should be used on [tprop] that are not unfolded (typically on recursive calls).
[@@__norm_tprop__] let tpr (#a : Type) (t : tprop a) : tprop a = tprop_of_vprop a (vprop_of_tprop t)
