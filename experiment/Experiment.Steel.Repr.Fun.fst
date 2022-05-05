module Experiment.Steel.Repr.Fun

module U   = Learn.Util
module L   = FStar.List.Pure
module Ll  = Learn.List
module Dl  = Learn.DList
module ST  = Experiment.Steel.Repr.ST
module Fin = FStar.Fin 

open Experiment.Steel.Repr.ST


type post_t (a : Type) = a -> Dl.ty_list
type post_v (#a : Type) (post : post_t a) (x : a) = Dl.dlist (post x)
type req_t = prop
type ens_t (a : Type) (post : post_t a) = (x : a) -> post_v post x -> prop

noeq
type prog_tree : (a : Type u#a) -> (post : post_t u#a u#b a) -> Type u#(1 + max a b) =
  | Tspec : (a : Type u#a) -> (post : post_t a) ->
            (req : req_t) -> (ens : ens_t a post) ->
            prog_tree a post
  | Tret   : (a : Type u#a) -> (x : a) -> (post : post_t a) -> (sl : post_v post x) ->
             prog_tree a post
  | Tbind  : (a : Type u#a) -> (b : Type u#a) ->
             (itm : post_t a) -> (post : post_t b) ->
             (f : prog_tree a itm) -> (g : ((x : a) -> (sl : post_v itm x) -> prog_tree b post)) ->
             prog_tree b post
  | TbindP : (a : Type u#a) -> (b : Type u#a) ->
             (post : post_t b) ->
             (wp : pure_wp a) -> (x : unit -> PURE a wp) -> (g : a -> prog_tree b post) ->
             prog_tree b post

let rec tree_req (#a : Type) (#post : post_t a) (t : prog_tree a post)
  : Tot req_t (decreases t)
  = match t with
  | Tspec _ _  req _ ->
             req
  | Tret _ _ _ _ ->
             True
  | Tbind a _  itm _  f g ->
             tree_req f /\
               (forall (x : a) (sl : post_v itm x) . tree_ens f x sl ==> tree_req (g x sl))
  | TbindP a _  _  wp _ g ->
             wp (fun (x : a) -> tree_req (g x)) /\ True

and tree_ens (#a : Type) (#post : post_t a) (t : prog_tree a post)
  : Tot (ens_t a post) (decreases t)
  = match t with
  | Tspec _ _  _ ens ->
             ens
  | Tret _ x  post0 sl ->
             (fun x' (sl' : post_v post x') -> x' == x /\ sl' == sl)
  | Tbind a _  itm post0  f g ->
             (fun y (sl2 : post_v post y) ->
               (exists (x : a) (sl1 : post_v itm x) .
                 tree_ens f x sl1 /\ tree_ens (g x sl1) y sl2))
  | TbindP a _  post0  wp _ g ->
             (fun y (sl1 : post_v post y) ->
               (exists (x : a) . as_ensures wp x /\ tree_ens (g x) y sl1))


(*** Repr.ST --> Repr.Fun *)

module T = FStar.Tactics
open FStar.Calc
open Learn.Logic

#push-options "--fuel 1 --ifuel 1"

type post_src (pre_n : nat) (post_n : nat) = Fin.fin post_n -> option (Fin.fin pre_n)

let post_src_of_shape (#pre_n : nat) (#post_n : nat) (s : ST.shape_tree pre_n post_n)
  : Tot (post_src pre_n post_n)
  = match s with
  | Sequiv n p ->
           (fun i -> Some (p i))
  | Sspec  pre_n post_n frame_n ->
           (fun i -> if i < post_n then None else Some (i - post_n + pre_n))
  | Sret   n ->
           (fun i -> None)
  | Sbind  pre_n itm_n post_n f g ->
            // bind returns all the selectors because with the current hypothesis, we need a value of the bound
            // type in order to prove that the propagated value (through g and f) has the correct type
           (fun i -> None)
  | SbindP pre_n post_n g ->
           (fun i -> None)

let post_src_ty
      (#a : Type) (#pre : ST.pre_t) (#post : ST.post_t a) (t : ST.prog_tree a pre post)
      (s : ST.prog_shape t) (x : a) (i : Fin.fin (L.length (post x)))
  : Lemma (requires Some? (post_src_of_shape s.shp i))
          (ensures  L.index (post x) i == L.index pre (Some?.v (post_src_of_shape s.shp i)))
  = match t with
    | ST.Tequiv _ _ _ -> ()
    | ST.Tspec  _ pre post frame _ _ ->
             Ll.append_index pre frame (i - (L.length (post x)) + (L.length pre));
             Ll.append_index (post x) frame i
    | ST.Tret _ _ _ | ST.Tbind _ _  _ _ _  _ _ | ST.TbindP _ _  _ _  _ _ _ -> ()

noeq
type post_bij_t' (#pre_n : nat) (#post_n : nat) (s : post_src pre_n post_n) = {
  post'_n : nat;
  post'_f : (i : Fin.fin post_n {None? (s i)}) -> Fin.fin post'_n;
  post'_g : Fin.fin post'_n -> (i : Fin.fin post_n  {None? (s i)});
}

type post_bij_t (#pre_n : nat) (#post_n : nat) (s : post_src pre_n post_n) =
  r : post_bij_t' s {
    (forall (i : Fin.fin post_n {None? (s i)}) . {:pattern (r.post'_g (r.post'_f i))}
      r.post'_g (r.post'_f i) = i) /\
    (forall (j : Fin.fin r.post'_n) . {:pattern (r.post'_f (r.post'_g j))}
      r.post'_f (r.post'_g j) = j)
  }

let rec mk_post_bij (#pre_n : nat) (#post_n : nat) (s : post_src pre_n post_n)
  : Tot (post_bij_t s) (decreases post_n)
  = if post_n = 0 then {
       post'_n = 0;
       post'_f = (fun _ -> false_elim ());
       post'_g = (fun _ -> false_elim ())}
    else
      let s' : post_src pre_n (post_n - 1) = fun i -> s (i+1) in
      let p' = mk_post_bij s' in
      match s 0 with
      | Some _ -> { post'_n = p'.post'_n;
                   post'_f = (fun i -> p'.post'_f (i-1));
                   post'_g = (fun j -> p'.post'_g j + 1)}
      | None   -> { post'_n = p'.post'_n + 1;
                   post'_f = (fun i -> if i = 0 then 0 else (p'.post'_f (i-1) + 1));
                   post'_g = (fun j -> if j = 0 then 0 else (p'.post'_g (j-1) + 1))}

let post_bij (#post_n : nat) (#pre_n : nat) (s : ST.shape_tree pre_n post_n)
  : Tot (post_bij_t (post_src_of_shape s))
  = match s with
  | Sequiv n p ->
           { post'_n = 0; post'_f = (fun _ -> false_elim ()); post'_g = (fun _ -> false_elim ()) }
  | Sspec  pre_n post_n frame_n ->
           { post'_n = post_n;
             post'_f = (fun (i : Fin.fin (post_n + frame_n) {None? (post_src_of_shape s i)}) -> i);
             post'_g = (fun j -> j) }
  | Sret   n ->
           { post'_n = n; post'_f = (fun i -> i); post'_g = (fun j -> j) }
  | Sbind  pre_n itm_n post_n f g ->
           { post'_n = post_n; post'_f = (fun i -> i); post'_g = (fun j -> j) }
  | SbindP pre_n post_n g ->
           { post'_n = post_n; post'_f = (fun i -> i); post'_g = (fun j -> j) }


let post_Fun_of_ST
      (#a : Type u#a) (post : ST.post_t u#a u#b a)
      (#pre_n #post_n : nat) (s : ST.shape_tree pre_n post_n {post_has_len post post_n})
  : post_t u#a u#b a
  = let p' = post_bij s in
    fun (x : a) -> Ll.initi 0 p'.post'_n (fun i -> L.index (post x) (p'.post'_g i))

// TODO? define with post : ty_list
let sel_Fun_of_ST
      (#a : Type u#a) (post : ST.post_t u#a u#b a)
      (#pre_n #post_n : nat) (s : ST.shape_tree pre_n post_n {post_has_len post post_n})
      (x : a) (post_val : Dl.dlist (post x))
  : post_v (post_Fun_of_ST post s) x
  = let p' = post_bij s in
    Dl.initi 0 p'.post'_n _ (fun i -> Dl.index post_val (p'.post'_g i))

unfold
let return_Fun_post'_of_ST
      (#a : Type u#a) (post : ST.post_t u#a u#b a)
      (#pre_n #post_n : nat) (s : ST.shape_tree pre_n post_n {post_has_len post post_n})
      (x : a) (post_val : Dl.dlist (post x))
  : prog_tree a (post_Fun_of_ST post s)
  = Tret a x (post_Fun_of_ST post s) (sel_Fun_of_ST post s x post_val)

// TODO? remove the dependency in [t]
let sel_ST_of_Fun
      (#a : Type) (#pre : ST.pre_t) (#post : ST.post_t a) (t : ST.prog_tree a pre post)
      (s : ST.prog_shape t)
      (sl0 : Dl.dlist pre) (x : a) (sl1' : post_v (post_Fun_of_ST post s.shp) x)
  : Dl.dlist (post x)
  =
    let p' = post_bij s.shp in
    Dl.initi_ty (post x)
             (fun i -> match post_src_of_shape s.shp i with
                    | Some j -> (**) post_src_ty t s x i;
                               U.cast (L.index (post x) i)
                                      (Dl.index sl0 j)
                    | None   -> U.cast (L.index (post x) i)
                                      (Dl.index sl1' (p'.post'_f i)))

#push-options "--z3rlimit 20"
let sel_Fun_ST_Fun
      (#a : Type) (#pre : ST.pre_t) (#post : ST.post_t a) (t : ST.prog_tree a pre post)
      (s : ST.prog_shape t)
      (sl0 : Dl.dlist pre) (x : a) (sl1' : post_v (post_Fun_of_ST post s.shp) x)
  : Lemma (sel_Fun_of_ST post s.shp x (sel_ST_of_Fun t s sl0 x sl1') == sl1')
  = Dl.dlist_extensionality
         (sel_Fun_of_ST post s.shp x (sel_ST_of_Fun t s sl0 x sl1')) sl1'
    begin fun i ->
      let p' = post_bij s.shp in
      let post_ST = sel_ST_of_Fun t s sl0 x sl1' in
      calc (==) {
        Dl.index (sel_Fun_of_ST post s.shp x post_ST) i;
      == {}
        U.cast (L.index (post_Fun_of_ST post s.shp x) i)
          (Dl.index post_ST ((post_bij s.shp).post'_g i));
      == {}
        Dl.index sl1' ((post_bij s.shp).post'_f ((post_bij s.shp).post'_g i));
      == {}
        Dl.index sl1' i;
      }
   end
#pop-options


let post_Fun_of_ST__spec
      (#a : Type) (post : ST.post_t a) (frame : Dl.ty_list)
      (pre_n : nat) (post_n : nat {post_has_len post post_n})
  : Lemma (ensures post_Fun_of_ST (ST.frame_post post frame) (Sspec pre_n post_n (L.length frame))
                == U.eta post)
  =
    let post' = post_Fun_of_ST (ST.frame_post post frame) (Sspec pre_n post_n (L.length frame)) in
    U.funext_eta post' (U.eta post)
         (assert (post' == U.eta post') by T.(trefl ())) (_ by T.(trefl ()))
         (fun x -> Ll.list_extensionality (post' x) (post x)
           (fun i -> Ll.append_index (post x) frame i))

let post_Fun_of_ST__ret
      (#a : Type) (post : ST.post_t a) (post_n : nat {post_has_len post post_n})
  : Lemma (ensures post_Fun_of_ST post (Sret post_n) == U.eta post)
  =
    let post' = post_Fun_of_ST post (Sret post_n) in
    U.funext_eta post' (U.eta post)
         (assert (post' == U.eta post') by T.(trefl ())) (_ by T.(trefl ()))
         (fun x -> Ll.list_extensionality (post' x) (post x) (fun i -> ()))


(* TODO? markers *)
let rec repr_Fun_of_ST
          (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
          (t : ST.prog_tree a pre post)
  : Tot ((s : ST.prog_shape t) -> Dl.dlist pre -> prog_tree a (post_Fun_of_ST post s.shp))
        (decreases t)
  = ST.match_prog_tree t
      (fun a pre post t -> (s : ST.prog_shape t) -> Dl.dlist pre ->
         prog_tree a (post_Fun_of_ST post s.shp))
    begin fun (*ST.Tequiv*) pre post0 p -> fun s sl0 ->
            Tret U.unit' U.Unit' (fun _ -> []) Dl.DNil
    end
    begin fun (*ST.Tspec*) a pre post frame req ens -> fun s sl0' ->
            (**) let Sspec _ post_n _ = s.shp in
            (**) post_Fun_of_ST__spec post frame (L.length pre) post_n;
            (**) let post'  = post_Fun_of_ST (ST.frame_post post frame) s.shp in
            let sl0 : Dl.dlist pre = (Dl.splitAt_ty pre frame sl0')._1 in
            Tspec a (U.eta post) (req sl0) (ens sl0) <: prog_tree a post'
    end
    begin fun (*ST.Tret*) a x post -> fun s sl ->
            (**) let Sret post_n = s.shp in
            (**) post_Fun_of_ST__ret post post_n;
            U.cast (prog_tree a (post_Fun_of_ST post s.shp)) (Tret a x (U.eta post) sl)
    end
    begin fun (*ST.Tbind*) a b pre itm post f g -> fun s sl0 ->
            (**) let Sbind _ itm_n post_n s_f s_g = s.shp in
            (**) let shp_f = ST.mk_prog_shape f s_f in
            Tbind a b  _ _ (repr_Fun_of_ST f shp_f sl0) (fun x sl1' ->
            (**) let shp_g : prog_shape (g x) = ST.mk_prog_shape (g x) s_g in
            let sl1 = sel_ST_of_Fun f shp_f sl0 x sl1' in
            Tbind b b  (post_Fun_of_ST post #(L.length (itm x)) s_g) _
                       (repr_Fun_of_ST (g x) shp_g sl1) (fun y sl2' ->
            let sl2 = sel_ST_of_Fun (g x) shp_g sl1 y sl2' in
            return_Fun_post'_of_ST post s.shp y sl2))
    end
    begin fun (*ST.TbindP*) a b pre post wp f g -> fun s sl0 ->
            (**) let SbindP _ post_n s_g = s.shp in
            TbindP a b _ wp f (fun x ->
            (**) let shp_g : prog_shape (g x) = ST.mk_prog_shape (g x) s_g in
            Tbind  b b (post_Fun_of_ST post #(L.length #Type pre) s_g) _
                       (repr_Fun_of_ST (g x) shp_g sl0) (fun y sl1' ->
            let sl1 = sel_ST_of_Fun (g x) shp_g sl0 y sl1' in
            return_Fun_post'_of_ST post s.shp y sl1))
    end
    
#pop-options


(***** soundness of ST --> Fun *)

#push-options "--fuel 1 --ifuel 0"

let post_eq_src (#pre #post : Dl.ty_list) (sl0 : Dl.dlist pre) (sl1 : Dl.dlist post)
                (s : post_src (L.length pre) (L.length post))
  : prop
  = forall (i : Fin.fin (L.length post)) .
      Some? (s i) ==> Dl.index sl1 i === Dl.index sl0 (Some?.v (s i))

let sel_ST_of_Fun_eq_src
      #a #pre #post (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Dl.dlist pre) (x : a) (sl1' : post_v (post_Fun_of_ST post s.shp) x)
  : Lemma (post_eq_src sl0 (sel_ST_of_Fun t s sl0 x sl1') (post_src_of_shape s.shp))
  = introduce forall (i : Fin.fin s.post_len) .
      Some? (post_src_of_shape s.shp i) ==>
      Dl.index (sel_ST_of_Fun t s sl0 x sl1') i === Dl.index sl0 (Some?.v (post_src_of_shape s.shp i))
    with introduce _ ==> _
    with _ . post_src_ty t s x i

#push-options "--z3rlimit 20"
let post_eq_src_ST_Fun_ST
      #a #pre #post  (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Dl.dlist pre) (x : a) (sl1 : Dl.dlist (post x))
  : Lemma (requires post_eq_src sl0 sl1 (post_src_of_shape s.shp))
          (ensures  sel_ST_of_Fun t s sl0 x (sel_Fun_of_ST post s.shp x sl1) == sl1)
  =
    Dl.dlist_extensionality (sel_ST_of_Fun t s sl0 x (sel_Fun_of_ST post s.shp x sl1)) sl1
    begin fun i ->
      match post_src_of_shape s.shp i with
      | Some j -> post_src_ty t s x i;
                 calc (==) {
                   Dl.index (sel_ST_of_Fun t s sl0 x (sel_Fun_of_ST post s.shp x sl1)) i;
                 == {}
                   U.cast (L.index (post x) i) (Dl.index sl0 j);
                 == {(*by [post_eq_src] *)}
                   Dl.index sl1 i;
                 }
      | None -> ()
    end
#pop-options

(* TODO? def de post_eq_src *)
let post_eq_src_iff
      #a #pre #post (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Dl.dlist pre) (x : a) (sl1 : Dl.dlist (post x))
  : Lemma (post_eq_src sl0 sl1 (post_src_of_shape s.shp)
           <==> sl1 == sel_ST_of_Fun t s sl0 x (sel_Fun_of_ST post s.shp x sl1))
  = sel_ST_of_Fun_eq_src t s sl0 x (sel_Fun_of_ST post s.shp x sl1);
    FStar.Classical.move_requires (post_eq_src_ST_Fun_ST t s sl0 x) sl1


unfold
let req_equiv #a #pre #post (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Dl.dlist pre)
  : prop
  = ST.tree_req t sl0 <==> tree_req (repr_Fun_of_ST t s sl0)

unfold
let ens_equiv #a #pre #post (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Dl.dlist pre) (res : a) (sl1 : Dl.dlist (post res))
  : prop
  = ST.tree_ens t sl0 res sl1 <==>
   (post_eq_src sl0 sl1 (post_src_of_shape s.shp) /\
    tree_ens (repr_Fun_of_ST t s sl0) res (sel_Fun_of_ST post s.shp res sl1))

let ens_equiv_rev #a #pre #post (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
      (sl0 : Dl.dlist pre) (res : a) (sl1' : post_v (post_Fun_of_ST post s.shp) res)
  : Lemma (requires ens_equiv t s sl0 res (sel_ST_of_Fun t s sl0 res sl1'))
          (ensures  ST.tree_ens t sl0 res (sel_ST_of_Fun t s sl0 res sl1') <==>
                    tree_ens (repr_Fun_of_ST t s sl0) res sl1')
  =
    sel_ST_of_Fun_eq_src t s sl0 res sl1';
    sel_Fun_ST_Fun t s sl0 res sl1'

#push-options "--z3rlimit 10"
let repr_Fun_of_ST_ens__Tspec a pre post frame req ens s sl0 x sl1
  : Lemma (ensures ens_equiv (ST.Tspec a pre post frame req ens) s sl0 x sl1)
  =
    let Sspec _ post_n _ = s.shp in
    post_Fun_of_ST__spec post frame (L.length pre) post_n;
    let sl0', frame0 = Dl.splitAt_ty pre frame sl0 in
    let sl1', frame1 = Dl.splitAt_ty (post x) frame sl1 in

    Dl.splitAt_ty_append pre frame sl0;
    Dl.splitAt_ty_append (post x) frame sl1;

    Dl.dlist_extensionality
      (sel_Fun_of_ST (ST.frame_post post frame) s.shp x sl1) sl1'
      (fun i -> Dl.append_index sl1' frame1 i);
    
    introduce frame1 == frame0 ==>
            (forall (i : int {post_n <= i /\ i < post_n + L.length frame}) .
                Dl.index sl1 i === Dl.index sl0 (i - post_n + L.length pre))
      with _ . introduce forall (i : int {post_n <= i /\ i < post_n + L.length frame}) .
                   Dl.(index (append sl1' frame1)) i ===
                   Dl.(index (append sl0' frame0)) (i - post_n + L.length pre)
      with (Dl.append_index sl1' frame1 i;
            Dl.append_index sl0' frame0 (i - post_n + L.length pre));

    introduce (forall (i : int {post_n <= i /\ i < post_n + L.length frame}) .
                Dl.index sl1 i === Dl.index sl0 (i - post_n + L.length pre))
            ==> frame1 == frame0
      with _ . Dl.dlist_extensionality frame1 frame0 (fun i ->
        eliminate forall (i : int {post_n <= i /\ i < post_n + L.length frame}) .
                  Dl.index sl1 i === Dl.index sl0 (i - post_n + L.length pre)
          with (i + post_n);
        Dl.append_index sl1' frame1 (i + post_n);
        Dl.append_index sl0' frame0 (i + L.length pre))
#pop-options

#push-options "--z3rlimit 20"
// Quite long
let repr_Fun_of_ST_req__Tbind a b pre (itm : ST.post_t a) post
      f (g : (x : a) -> ST.prog_tree b (itm x) post)
      (s_f  : prog_shape f)
      (post_n : nat {ST.post_has_len post post_n})
      (shp_g : ST.shape_tree s_f.post_len post_n {forall (x : a) . ST.prog_has_shape (g x) shp_g})
      sl0
      (pre_eq_g  : (x : a) -> (sl1 : Dl.dlist (itm x)) ->
                   Lemma (req_equiv (g x) (ST.mk_prog_shape (g x) shp_g) sl1))
      (post_eq_f : (x : a) -> (sl1 : Dl.dlist (itm x)) ->
                   Lemma (requires ST.tree_req f sl0) (ensures ens_equiv f s_f sl0 x sl1))
  : Lemma
      (requires ST.tree_req f sl0 <==> tree_req (repr_Fun_of_ST f s_f sl0))
      (ensures  req_equiv (ST.Tbind a b pre itm post f g)
                          (ST.mk_prog_shape _ (Sbind _ _ _ s_f.shp shp_g)) sl0)
  =
    let t = ST.Tbind a b pre itm post f g in
    let s = ST.mk_prog_shape t (Sbind (L.length pre) s_f.post_len post_n s_f.shp shp_g) in
    let shp_f = ST.mk_prog_shape f s_f.shp in
    let r_f = repr_Fun_of_ST f shp_f sl0 in
    let s_g (x : a) = ST.mk_prog_shape (g x) shp_g in
    let r_g (x : a) (sl1 : Dl.dlist (itm x)) = repr_Fun_of_ST (g x) (s_g x) sl1 in
    let itm' = post_Fun_of_ST itm s_f.shp in
    
    assert (req_equiv t s sl0 == (
      (ST.tree_req f sl0 /\
      (forall (x : a) (sl1 : Dl.dlist (itm x)) .
        ST.tree_ens f sl0 x sl1 ==> ST.tree_req (g x) sl1))
    <==>
      (tree_req r_f /\
      (forall (x : a) (sl1' : post_v itm' x) .
        tree_ens r_f x sl1' ==>
      (let sl1 = sel_ST_of_Fun f s_f sl0 x sl1' in
        tree_req (r_g x sl1) /\
      (forall (y : b) (sl2' : post_v (post_Fun_of_ST post #(L.length (itm x)) shp_g) y) .
        tree_ens (r_g x sl1) y sl2' ==> True))))
    )) by T.(trefl ());


    introduce forall (x : a) . ST.tree_req f sl0 ==> (
      (forall (sl1 : Dl.dlist (itm x)) . ST.tree_ens f sl0 x sl1 ==> ST.tree_req (g x) sl1) <==>
      (forall (sl1' : post_v itm' x) .
        tree_ens r_f x sl1' ==>
        tree_req (r_g x (sel_ST_of_Fun f s_f sl0 x sl1'))))
      with introduce _ ==> _
      with _ . begin
        introduce forall (sl1 : Dl.dlist (itm x)) . ens_equiv f s_f sl0 x sl1
          with post_eq_f x sl1;
        FStar.Classical.forall_intro (post_eq_src_iff f s_f sl0 x);
        forall_morph_iff #(post_v itm' x)
          (fun sl1' -> ST.tree_ens f sl0 x (sel_ST_of_Fun f s_f sl0 x sl1') ==>
                    ST.tree_req (g x) (sel_ST_of_Fun f s_f sl0 x sl1'))
          (fun sl1' -> tree_ens r_f x sl1' ==>
                    tree_req (r_g x (sel_ST_of_Fun f s_f sl0 x sl1')))
          (fun sl1' -> ens_equiv_rev f s_f sl0 x sl1';
                    pre_eq_g x (sel_ST_of_Fun f s_f sl0 x sl1'))
      end
#pop-options

#push-options "--z3rlimit 60"
let repr_Fun_of_ST_ens__Tbind a b pre (itm : ST.post_t a) post
      f (g : (x : a) -> ST.prog_tree b (itm x) post)
      (s_f  : prog_shape f)
      (post_n : nat {ST.post_has_len post post_n})
      (shp_g : ST.shape_tree s_f.post_len post_n {forall (x : a) . ST.prog_has_shape (g x) shp_g})
      sl0 y sl2
      (post_eq_f : (x : a) -> (sl1 : Dl.dlist (itm x)) ->
                   Lemma (ens_equiv f s_f sl0 x sl1))
      (post_eq_g : (x : a) -> (sl1 : Dl.dlist (itm x)) ->
                   Lemma (requires ST.tree_req (g x) sl1)
                         (ensures ens_equiv (g x) (ST.mk_prog_shape (g x) shp_g) sl1 y sl2))
  : Lemma
      (requires ST.tree_req (ST.Tbind a b pre itm post f g) sl0)
      (ensures  ens_equiv (ST.Tbind a b pre itm post f g)
                          (ST.mk_prog_shape _ (Sbind _ _ _ s_f.shp shp_g)) sl0 y sl2)
  =
    let t = ST.Tbind a b pre itm post f g in
    let s = ST.mk_prog_shape t (Sbind (L.length pre) s_f.post_len post_n s_f.shp shp_g) in
    let shp_f = ST.mk_prog_shape f s_f.shp in
    let r_f = repr_Fun_of_ST f shp_f sl0 in
    let s_g (x : a) = ST.mk_prog_shape (g x) shp_g in
    let r_g (x : a) (sl1 : Dl.dlist (itm x)) = repr_Fun_of_ST (g x) (s_g x) sl1 in
    let itm'  = post_Fun_of_ST itm s_f.shp in
    let post'g = post_Fun_of_ST post shp_g in
    let post'  = post_Fun_of_ST post s.shp in
    let sl2' : post_v post' y = sel_Fun_of_ST post s.shp y sl2 in

    assert (ens_equiv t s sl0 y sl2 ==
      (ST.tree_req f sl0 /\
       (exists (x : a) (sl1 : Dl.dlist (itm x)) .
         ST.tree_ens f sl0 x sl1 /\ ST.tree_ens (g x) sl1 y sl2)
     <==>
      (post_eq_src sl0 sl2 (post_src_of_shape s.shp) /\
      ((exists (x : a) (sl1' : post_v itm' x) .
         tree_ens r_f x sl1' /\
       (let sl1 = sel_ST_of_Fun f shp_f sl0 x sl1' in
        let r_g = r_g x sl1 in
        (exists (yg : b) (sl2g : post_v (post_Fun_of_ST post #(L.length (itm x)) shp_g) yg) .
         tree_ens r_g yg sl2g /\
        (let sl2f : Dl.dlist (post yg) = sel_ST_of_Fun (g x) (s_g x) sl1 yg sl2g in
         tree_ens (Tret b yg post' (sel_Fun_of_ST post s.shp yg sl2f)) y sl2'
         ))))))
    )) by T.(trefl ());

    assert (ST.tree_req f sl0);
    assert (post_eq_src sl0 sl2 (post_src_of_shape s.shp));

    introduce forall (x : a) .
       (exists (sl1 : Dl.dlist (itm x)) . ST.tree_ens f sl0 x sl1 /\ ST.tree_ens (g x) sl1 y sl2)
    <==> (exists (sl1' : post_v itm' x) .
         tree_ens r_f x sl1' /\
       (let sl1 = sel_ST_of_Fun f s_f sl0 x sl1' in
        let r_g = r_g x sl1 in
        (exists (sl2g : post_v post'g y) .
         tree_ens r_g y sl2g /\
         sl2' == sel_Fun_of_ST post s.shp y (sel_ST_of_Fun (g x) (s_g x) sl1 y sl2g)
         )))
    with begin
      introduce forall (sl2g : post_v post'g y) (sl1 : Dl.dlist (itm x)) .
        sl2' == sel_Fun_of_ST post s.shp y (sel_ST_of_Fun (g x) (s_g x) sl1 y sl2g)
        <==> (sl2g == sel_Fun_of_ST post shp_g y sl2 /\
           post_eq_src sl1 sl2 (post_src_of_shape shp_g))
      with begin
        let sl2gST = sel_ST_of_Fun (g x) (s_g x) sl1 y sl2g in
        // [sel_Fun_of_ST post s y] is injective (for s = [Sbind _]), the inverse is sel_ST_of_Fun
        U.assert_by (sel_Fun_of_ST post s.shp y sl2 == sel_Fun_of_ST post s.shp y sl2gST
                  ==> sl2 == sl2gST)
          (fun () -> post_eq_src_ST_Fun_ST t s sl0 y sl2;
                     post_eq_src_ST_Fun_ST t s sl0 y sl2gST);
        sel_Fun_ST_Fun  (g x) (s_g x) sl1 y sl2g;
        post_eq_src_iff (g x) (s_g x) sl1 y sl2
      end;

      FStar.Classical.forall_intro (post_eq_f x);
      FStar.Classical.forall_intro (post_eq_src_iff f s_f sl0 x);

      exists_morph_iff #(post_v itm' x)
        (fun sl1' -> ST.tree_ens f sl0 x (sel_ST_of_Fun f s_f sl0 x sl1') /\
                  ST.tree_ens (g x) (sel_ST_of_Fun f s_f sl0 x sl1') y sl2)
        (fun sl1' -> tree_ens r_f x sl1' /\
                 (let sl1 = sel_ST_of_Fun f s_f sl0 x sl1' in
                  let r_g = r_g x sl1 in
                  post_eq_src sl1 sl2 (post_src_of_shape shp_g) /\
                  tree_ens r_g y (sel_Fun_of_ST post shp_g y sl2)))
        (fun sl1' ->
          let sl1 = sel_ST_of_Fun f s_f sl0 x sl1' in
          post_eq_f x sl1;
          ens_equiv_rev f s_f sl0 x sl1';
          FStar.Classical.move_requires (post_eq_g x) sl1)
    end
#pop-options

let repr_Fun_of_ST_ens__TbindP a b pre post
      wp f (g : a -> ST.prog_tree b pre post)
      (post_n : nat {ST.post_has_len post post_n})
      (shp_g : ST.shape_tree _ post_n {forall (x : a) . ST.prog_has_shape (g x) shp_g})
      sl0 y sl1
      (post_eq_g : (x : a) ->
                   Lemma (requires ST.tree_req (g x) sl0)
                         (ensures ens_equiv (g x) (ST.mk_prog_shape (g x) shp_g) sl0 y sl1))
  : Lemma
      (requires ST.tree_req (ST.TbindP a b pre post wp f g) sl0)
      (ensures  ens_equiv (ST.TbindP a b pre post wp f g)
                          (ST.mk_prog_shape _ (SbindP _ _ shp_g)) sl0 y sl1)
  =
    let t = ST.TbindP a b pre post wp f g in
    let s = ST.mk_prog_shape t (SbindP (L.length pre) post_n shp_g) in
    let s_g (x : a) = ST.mk_prog_shape (g x) shp_g in
    let r_g (x : a) = repr_Fun_of_ST (g x) (s_g x) sl0 in
    let post'g = post_Fun_of_ST post shp_g in
    let post'  = post_Fun_of_ST post s.shp in
    let sl1' : post_v post' y = sel_Fun_of_ST post s.shp y sl1 in

    assert (ens_equiv t s sl0 y sl1 == (
      (as_requires wp /\
      (exists (x : a) .
        as_ensures wp x /\ ST.tree_ens (g x) sl0 y sl1)
     <==>
      (post_eq_src sl0 sl1 (post_src_of_shape s.shp) /\
      (exists (x : a) .
       as_ensures wp x /\
      (exists (yg : b) (sl1g : post_v (post_Fun_of_ST post #(L.length #Type pre) shp_g) yg) .
       tree_ens (r_g x) yg sl1g /\
      (let sl1f = sel_ST_of_Fun (g x) (s_g x) sl0 yg sl1g in
       y == yg /\ sl1' == sel_Fun_of_ST post s.shp yg sl1f
      )))))
    )) by T.(trefl ());

    assert (post_eq_src sl0 sl1 (post_src_of_shape s.shp));
    let req_g x = ST.tree_req (g x) sl0 in
    assert (ST.tree_req (ST.TbindP a b pre post wp f g) sl0 == (wp req_g /\ True))
        by T.(trefl ());
    U.prop_equal (fun p -> p) (ST.tree_req (ST.TbindP a b pre post wp f g) sl0) (wp req_g /\ True);
    
    U.assert_by (as_requires wp)
      (fun () -> FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp);

    introduce forall (x : a {as_ensures wp x}) .
      (ST.tree_ens (g x) sl0 y sl1 <==>
      (exists (sl1g : post_v post'g y) .
         tree_ens (r_g x) y sl1g /\
         sl1' == sel_Fun_of_ST post s.shp y (sel_ST_of_Fun (g x) (s_g x) sl0 y sl1g)))
    with begin
      
      U.assert_by (ST.tree_req (g x) sl0)
        (fun () -> FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp);

      introduce forall (sl1g : post_v post'g y) .
        sl1' == sel_Fun_of_ST post s.shp y (sel_ST_of_Fun (g x) (s_g x) sl0 y sl1g)
        <==> (sl1g == sel_Fun_of_ST post shp_g y sl1 /\
            post_eq_src sl0 sl1 (post_src_of_shape shp_g))
       with begin
        let sl1gST = sel_ST_of_Fun (g x) (s_g x) sl0 y sl1g in
         U.assert_by (sel_Fun_of_ST post s.shp y sl1 == sel_Fun_of_ST post s.shp y sl1gST
                   ==> sl1 == sl1gST)
          (fun () -> post_eq_src_ST_Fun_ST t s sl0 y sl1;
                  post_eq_src_ST_Fun_ST t s sl0 y sl1gST);
        sel_Fun_ST_Fun (g x) (s_g x) sl0 y sl1g;
        post_eq_src_iff (g x) (s_g x) sl0 y sl1
       end;
       post_eq_g x
    end


#push-options "--z3rlimit 10"
let rec repr_Fun_of_ST_req
  (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
  (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
  (sl0 : Dl.dlist pre)
  : Lemma (ensures req_equiv t s sl0) (decreases t)
  = ST.match_prog_tree t
    (fun a pre post t -> (s : ST.prog_shape t) -> (sl0 : Dl.dlist pre) ->
       squash (ST.tree_req t sl0 <==> tree_req (repr_Fun_of_ST t s sl0)))
    (fun (*ST.Tequiv*) pre post0 p -> fun s sl0 -> ())
    (fun (*ST.Tspec*) a pre post frame req ens -> fun s sl0 -> ())
    (fun (*ST.Tret*) a x post -> fun s sl0 -> ())
    begin fun (*ST.Tbind*) a b pre itm post f g -> fun s sl0 ->
      let Sbind _ itm_n post_n shp_f shp_g = s.shp in
      let s_f = ST.mk_prog_shape f shp_f in
      let s_g (x : a) = ST.mk_prog_shape (g x) shp_g in
      repr_Fun_of_ST_req f s_f sl0;
      repr_Fun_of_ST_req__Tbind a b pre itm post f g s_f post_n shp_g sl0
        (fun x sl1 -> repr_Fun_of_ST_req (g x) (s_g x) sl1)
        (fun x sl1 -> repr_Fun_of_ST_ens f s_f sl0 x sl1)
    end
    begin fun (*ST.TbindP*) a b pre post wp f g -> fun s sl0 ->
      let SbindP _ post_n shp_g = s.shp in
      let s_g (x : a) = ST.mk_prog_shape (g x) shp_g in
      let pt0 x = ST.tree_req (g x) sl0 in
      let pt1 x = tree_req (repr_Fun_of_ST (g x) (s_g x) sl0) /\
                    (forall (y : b) (sl1' : post_v (post_Fun_of_ST post #(L.length #Type pre) shp_g) y) .
                    tree_ens (repr_Fun_of_ST (g x) (s_g x) sl0) y sl1' ==> True) in
      calc (<==>) {
        ST.tree_req (ST.TbindP a b pre post wp f g) sl0;
      <==> { _ by T.(apply_lemma (`U.iff_refl); trefl ()) }
        wp (fun x -> ST.tree_req (g x) sl0) /\ True;
      <==> {}
        wp pt0;
      <==> { wp_morph_iff wp pt0 pt1 (fun x -> repr_Fun_of_ST_req (g x) (s_g x) sl0) }
        wp pt1;
      <==> {}
        wp (fun x -> tree_req (repr_Fun_of_ST (g x) (ST.mk_prog_shape (g x) shp_g) sl0) /\
                (forall (y : b) (sl1' : post_v (post_Fun_of_ST post #(L.length #Type pre) shp_g) y) .
                tree_ens (repr_Fun_of_ST (g x) (ST.mk_prog_shape (g x) shp_g) sl0) y sl1' ==> True)) /\ True;
      <==> { _ by T.(apply_lemma (`U.iff_refl); trefl ())}
        tree_req (repr_Fun_of_ST (ST.TbindP a b pre post wp f g)
                                 (ST.mk_prog_shape _ (SbindP _ _ shp_g)) sl0);
      }
    end s sl0

and repr_Fun_of_ST_ens
  (#a : Type u#a) (#pre : ST.pre_t u#b) (#post : ST.post_t u#a u#b a)
  (t : ST.prog_tree a pre post) (s : ST.prog_shape t)
  (sl0 : Dl.dlist pre) (res : a) (sl1 : Dl.dlist (post res))
  : Lemma (requires  ST.tree_req t sl0)
          (ensures   ens_equiv t s sl0 res sl1)
          (decreases t)
  = ST.match_prog_tree t
    (fun a pre post t -> (s : ST.prog_shape t) ->
       (sl0 : Dl.dlist pre) -> (res : a) -> (sl1 : Dl.dlist (post res)) ->
       squash (ST.tree_req t sl0) ->
       squash (ens_equiv t s sl0 res sl1))
    begin fun (*ST.Tequiv*) pre post0 p -> fun s sl0 U.Unit' sl1 () ->
      introduce (forall (i : Fin.fin (L.length post0)) . Dl.index sl1 i === Dl.index sl0 (p i)) ==>
                sl1 == Dl.apply_perm_r p sl0
        with _ . Dl.dlist_extensionality sl1 (Dl.apply_perm_r p sl0) (fun _ -> ())
    end
    begin fun (*ST.Tspec*) a pre post frame req ens -> fun s sl0 x sl1 () ->
      repr_Fun_of_ST_ens__Tspec a pre post frame req ens s sl0 x sl1
    end
    begin fun (*ST.Tret*) a x post -> fun s sl0 x sl1 () ->
      let Sret post_n = s.shp in
      post_Fun_of_ST__ret post post_n;
      Dl.dlist_extensionality (sel_Fun_of_ST post s.shp x sl1) sl1 (fun _ -> ())
    end
    begin fun (*ST.Tbind*) a b pre itm post f g -> fun s sl0 y sl2 _ ->
      let Sbind _ itm_n post_n shp_f shp_g = s.shp in
      let s_f = ST.mk_prog_shape f shp_f in
      let s_g (x : a) = ST.mk_prog_shape (g x) shp_g in
      repr_Fun_of_ST_ens__Tbind a b pre itm post f g s_f post_n shp_g sl0 y sl2
        (fun x sl1 -> repr_Fun_of_ST_ens f s_f sl0 x sl1)
        (fun x sl1 -> repr_Fun_of_ST_ens (g x) (s_g x) sl1 y sl2)
    end
    begin fun (*ST.TbindP*) a b pre post wp f g -> fun s sl0 y sl1 _ ->
      let SbindP _ post_n shp_g = s.shp in
      let s_g (x : a) = ST.mk_prog_shape (g x) shp_g in
      repr_Fun_of_ST_ens__TbindP a b pre post wp f g post_n shp_g sl0 y sl1
        (fun x -> repr_Fun_of_ST_ens (g x) (s_g x) sl0 y sl1)
    end s sl0 res sl1 ()
#pop-options

#pop-options


(*** Steel.Repr.Fun --> Repr.Fun *)

module Uv  = FStar.Universe
module Fun = Experiment.Repr.Fun

noeq
type sl_tys_t : Type u#(max a b + 1)= {
  val_t : Type u#a;
  sel_t : post_t u#a u#b val_t
}

noeq
type sl_tys_v (ty : sl_tys_t u#a u#b) : Type u#(max a (b + 1)) = {
  val_v : ty.val_t;
  sel_v : Dl.dlist (ty.sel_t val_v)
}

let rec forall_dlist (ty : Dl.ty_list) (f : Dl.dlist ty -> Type0)
  : Pure Type0 (requires True) (ensures fun p -> p <==> (forall (xs : Dl.dlist ty) . f xs)) (decreases ty)
  = match ty with
  | [] -> f Dl.DNil
  | t0 :: ts -> assert (forall (xs' : Dl.dlist ty) . exists (x : t0) (xs : Dl.dlist ts) .
                         xs' == Dl.DCons t0 x ts xs);
             (forall (x : t0) . forall_dlist ts (fun xs -> f (Dl.DCons t0 x ts xs)))

let sl_all (ty : sl_tys_t) (f : sl_tys_v ty -> Type0)
  : Pure Type0 (requires True) (ensures fun p -> p <==> (forall (x : sl_tys_v ty) . f x))
  =
    assert (forall (x : sl_tys_v ty) . x == {val_v = x.val_v; sel_v = x.sel_v});
   (forall (val_v : ty.val_t) . forall_dlist (ty.sel_t val_v) (fun sel_v -> f ({val_v; sel_v})))

let rec exists_dlist (ty : Dl.ty_list) (f : Dl.dlist ty -> Type0)
  : Pure Type0 (requires True) (ensures fun p -> p <==> (exists (xs : Dl.dlist ty) . f xs)) (decreases ty)
  = match ty with
  | [] -> f Dl.DNil
  | t0 :: ts -> assert (forall (xs' : Dl.dlist ty) . exists (x : t0) (xs : Dl.dlist ts) .
                         xs' == Dl.DCons t0 x ts xs);
             (exists (x : t0) . exists_dlist ts (fun xs -> f (Dl.DCons t0 x ts xs)))

let sl_ex (ty : sl_tys_t) (f : sl_tys_v ty -> Type0)
  : Pure Type0 (requires True) (ensures fun p -> p <==> (exists (x : sl_tys_v ty) . f x))
  =
    assert (forall (x : sl_tys_v ty) . x == {val_v = x.val_v; sel_v = x.sel_v});
   (exists (val_v : ty.val_t) . exists_dlist (ty.sel_t val_v) (fun sel_v -> f ({val_v; sel_v})))


let rec arw_dlist (src : Dl.ty_list u#s) (dst : Type u#d)
  : Tot (Type u#(max s d)) (decreases src)
  = match src with
  | [] -> Uv.raise_t dst
  | t0 :: ts -> (t0 -> arw_dlist ts dst)

let partial_app_dlist (src0 : Type u#s) (src : Dl.ty_list u#s) (dst : Type u#d) (f : Dl.dlist (src0 :: src) -> dst)
                      (x : src0) (xs : Dl.dlist src) : dst
  = f Dl.(DCons src0 x src xs)

let rec lam_dlist (src : Dl.ty_list u#s) (dst : Type u#d) (f : Dl.dlist src -> dst)
  : Tot (arw_dlist src dst) (decreases src)
  = match src with
  | [] -> Uv.raise_val (f Dl.DNil)
  | t0 :: ts -> (fun (x : t0) -> lam_dlist ts dst (partial_app_dlist t0 ts dst f x))

let rec app_dlist (#src : Dl.ty_list u#s) (#dst : Type u#d) (f : arw_dlist src dst) (x : Dl.dlist src)
  : Tot dst (decreases src)
  = match (|src, f, x|) <: (src : Dl.ty_list & arw_dlist src dst & Dl.dlist src) with
  | (|[],      v, Dl.DNil|)           -> Uv.downgrade_val v
  | (|t0 :: ts, f, Dl.DCons _ x _ xs|) -> app_dlist #ts #dst (f x) xs

let rec app_lam_dlist (src : Dl.ty_list u#s) (dst : Type u#d) (f : Dl.dlist src -> dst) (x : Dl.dlist src)
  : Lemma (ensures app_dlist (lam_dlist src dst f) x == f x)
          (decreases src)
          [SMTPat (app_dlist (lam_dlist src dst f) x)]
  = match x with
  | Dl.DNil -> ()
  | Dl.DCons t0 x ts xs -> app_lam_dlist ts dst (partial_app_dlist t0 ts dst f x) xs

let sl_arw (src : sl_tys_t u#a u#b) (dst : Type u#d) : Type =
  (x : src.val_t) -> arw_dlist (src.sel_t x) dst

let sl_lam (src : sl_tys_t u#a u#b) (dst : Type u#d) (f : (x : src.val_t) -> (xs : Dl.dlist (src.sel_t x)) -> dst)
  : sl_arw src dst
  = fun (x : src.val_t) -> lam_dlist (src.sel_t x) dst (f x)

let sl_app (#src : sl_tys_t u#a u#b) (#dst : Type u#d) (f : sl_arw src dst) (x : sl_tys_v src) : dst
  = app_dlist (f x.val_v) x.sel_v

let sl_app_lam (src : sl_tys_t u#a u#b) (dst : Type u#d)
               (f : (x : src.val_t) -> (xs : Dl.dlist (src.sel_t x)) -> dst) (x : sl_tys_v src)
  : Lemma (ensures sl_app (sl_lam src dst f) x == f x.val_v x.sel_v)
          [SMTPat (sl_app (sl_lam src dst f) x)]
  = ()


let sl_tys : Fun.tys u#(max a b + 1) u#(max a (b + 1)) = {
  t = sl_tys_t u#a u#b;
  v = sl_tys_v u#a u#b;
  unit = {val_t = U.unit'; sel_t = (fun _ -> [])};
  emp  = {val_v = U.Unit'; sel_v = Dl.DNil};
  all  = sl_all;
  ex   = sl_ex;
}


let rec repr_Fun_of_Steel (#val_t : Type u#a) (#sel_t : post_t u#a u#b val_t) (t : prog_tree val_t sel_t)
  : Tot (Fun.prog_tree u#(max a b + 1) u#(max a (b + 1)) u#a (sl_tys u#a u#b) ({val_t; sel_t}))
        (decreases t)
  = match t with
  | Tspec a post req ens ->
          Fun.Tspec ({val_t = a; sel_t = post}) req
             (sl_app (sl_lam ({val_t = a; sel_t = post}) prop ens))
  | Tret a x post sl ->
          Fun.Tret #sl_tys ({val_t = a; sel_t = post}) ({val_v = x; sel_v = sl})
  | Tbind a b itm post f g ->
          Fun.Tbind _ _
            (repr_Fun_of_Steel f)
            (sl_app (sl_lam _ _ (fun v sl -> repr_Fun_of_Steel (g v sl))))
  | TbindP a b post wp f g ->
           Fun.TbindP a ({val_t = b; sel_t = post}) wp f (fun (x : a) -> repr_Fun_of_Steel (g x))


(***** soundness of Steel.Fun --> Fun *)

#push-options "--z3rlimit 40 --ifuel 1 --fuel 1"
let rec repr_Fun_of_Steel_req #val_t #sel_t (t : prog_tree val_t sel_t)
  : Lemma (ensures tree_req t <==> Fun.tree_req (repr_Fun_of_Steel t))
          (decreases t)
  = match t with
  | Tspec a post req ens -> ()
  | Tret a x post sl -> ()
  | Tbind a b itm post f g ->
          repr_Fun_of_Steel_req f;
          introduce forall (x : a) (sl1 : post_v itm x) .
                    (tree_ens f x sl1   <==> Fun.tree_ens (repr_Fun_of_Steel f) ({val_v=x; sel_v=sl1})) /\
                    (tree_req (g x sl1) <==> Fun.tree_req (repr_Fun_of_Steel (g x sl1)))
            with (repr_Fun_of_Steel_ens f x sl1; repr_Fun_of_Steel_req (g x sl1))
  | TbindP a b post wp f g ->
          calc (<==>) {
            tree_req (TbindP a b post wp f g);
          <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
            wp (fun x -> tree_req (g x)) /\ True;
          <==> {wp_morph_iff wp (fun x -> tree_req (g x)) (fun x -> Fun.tree_req (repr_Fun_of_Steel (g x)))
                              (fun x -> repr_Fun_of_Steel_req (g x))}
            wp (fun x -> Fun.tree_req (repr_Fun_of_Steel (g x)));
          <==> {_ by T.(apply_lemma (`U.iff_refl); trefl ())}
            Fun.tree_req (repr_Fun_of_Steel (TbindP a b post wp f g));
          }

and repr_Fun_of_Steel_ens #val_t #sel_t (t : prog_tree val_t sel_t)
                          (val_v : val_t) (sel_v : Dl.dlist (sel_t val_v))
  : Lemma (ensures tree_ens t val_v sel_v <==> Fun.tree_ens (repr_Fun_of_Steel t) ({val_v; sel_v}))
          (decreases t)
  = match t with
  | Tspec a post req ens ->
          assert (tree_ens (Tspec a post req ens) val_v sel_v == ens val_v sel_v)
               by T.(trefl ());
          assert (Fun.tree_ens (repr_Fun_of_Steel (Tspec a post req ens)) ({val_v; sel_v})
               == sl_app (sl_lam ({val_t = a; sel_t = post}) prop ens) ({val_v; sel_v}))
               by T.(trefl ())
  | Tret a x post sl -> ()
  | Tbind a b itm post f g ->
          assert (tree_ens (Tbind a b itm post f g) val_v sel_v
               == (exists (x : a) (sl1 : post_v itm x) . tree_ens f x sl1 /\ tree_ens (g x sl1) val_v sel_v) )
               by T.(trefl ());
          assert (Fun.tree_ens (repr_Fun_of_Steel (Tbind a b itm post f g)) ({val_v; sel_v})
               == sl_tys.ex ({val_t=a; sel_t=itm}) (fun (x_sl1 : sl_tys_v ({val_t=a; sel_t=itm})) ->
                     Fun.tree_ens (repr_Fun_of_Steel f) x_sl1 /\
                     Fun.tree_ens
                      (sl_app (sl_lam _ _ (fun v sl -> repr_Fun_of_Steel (g v sl))) x_sl1) ({val_v; sel_v})))
               by T.(trefl ());
          introduce forall (x : a) (sl1 : post_v itm x) .
                    (tree_ens f x sl1   <==> Fun.tree_ens (repr_Fun_of_Steel f) ({val_v=x; sel_v=sl1})) /\
                    (tree_ens (g x sl1) val_v sel_v <==> Fun.tree_ens (repr_Fun_of_Steel (g x sl1)) ({val_v; sel_v}))
            with (repr_Fun_of_Steel_ens f x sl1; repr_Fun_of_Steel_ens (g x sl1) val_v sel_v)
  | TbindP a b post wp f g ->
          assert (tree_ens (TbindP a b post wp f g) val_v sel_v
              == (exists (x : a) . as_ensures wp x /\ tree_ens (g x) val_v sel_v))
            by T.(trefl ());
          assert (Fun.tree_ens (repr_Fun_of_Steel (TbindP a b post wp f g)) ({val_v; sel_v})
              == (exists (x : a) . as_ensures wp x /\ Fun.tree_ens (repr_Fun_of_Steel (g x)) ({val_v; sel_v})))
            by T.(trefl ());
          introduce forall (x : a) .
                    (tree_ens (g x) val_v sel_v <==> Fun.tree_ens (repr_Fun_of_Steel (g x)) ({val_v; sel_v}))
            with repr_Fun_of_Steel_ens (g x) val_v sel_v
#pop-options
