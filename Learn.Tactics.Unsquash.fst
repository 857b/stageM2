module Learn.Tactics.Unsquash

module F = FStar.Reflection.Formula

open FStar.Tactics

private
let __pose (a:Type) (b:Type) (x : a) (f : a -> b) : b = f x

(* TODO? force the instantiation of [b] *)
let pose' (t:term) : Tac binder =
    apply (`__pose);
    exact t;
    intro ()


(* [allI] : introduces [forall (x : t) . p x] into [x:t |- squash (p x)] *)

let allI : unit -> Tac binder = forall_intro

(* [allD] : destructs [forall (x : t) . p x] into [(x : t) -> squash (p x)] *)

private
let __forall_usq #t (#pred : t -> Type0) (h : (forall x. pred x)) : x:t -> squash (pred x) =
  fun x -> ()

private
let __forall_usq_sq #t (#pred : t -> Type0) (h : squash (forall x. pred x)) : x:t -> squash (pred x) =
  fun x -> ()

let allD_keep (fa : term) : Tac binder =
  try pose' (`__forall_usq_sq (`#fa)) with | _ ->
  try pose' (`__forall_usq (`#fa)) with | _ ->
  fail "allD: could not unsquash"

let allD (fa : binder) : Tac binder =
  let faa = allD_keep fa in
  clear fa;
  faa

(* [impI] : introduces [a ==> b] with [_ : squash a |- squash b] *)

private let imp_intro_lem (#a #b:Type) (prf : squash a -> squash b) : Lemma (a ==> b)
  = introduce a ==> b with pf_a . prf pf_a

let impI () : Tac binder =
  apply_lemma (`imp_intro_lem);
  intro ()

(* [impD] : destructs [a ==> b] into [squash a -> squash b] *)

private
let __imp_usq (#a #b : Type) (h : (a ==> b)) : squash a -> squash b =
  fun pa -> ()

private
let __imp_usq_sq (#a #b : Type) (h : squash (a ==> b)) : squash a -> squash b =
  fun pa -> ()

let impD_keep (ip : term) : Tac binder =
  try pose' (`__imp_usq_sq (`#ip)) with | _ ->
  try pose' (`__imp_usq (`#ip)) with | _ ->
  fail "impD: could not unsquash"

let impD (ip : binder) : Tac binder =
  let rt = impD_keep ip in
  clear ip;
  rt

(* [andI] : introduces [a /\ b] with [squash a] and [squash b] *)

let andI : unit -> Tac unit = split

(* [andD] : destrucs [a /\ b] into [squash a, squash b]
   Also works if the goal is not a squash. *)

private
let __and_usq (#a #b #c : Type) (h : (a /\ b)) (ct : squash a -> squash b -> c) : c =
  ct () ()

private
let __and_usq_sq (#a #b #c : Type) (h : squash (a /\ b)) (ct : squash a -> squash b -> c) : c =
  ct () ()

let andD_keep (cj : term) : Tac (binder & binder) =
  begin try apply (`__and_usq_sq (`#cj)) with | _ ->
        try apply (`__and_usq (`#cj)) with | _ ->
        fail "andD: could not unsquash"
  end;
  let hl = intro () in let hr = intro () in
  hl,hr

let andD (b : binder) : Tac (binder & binder) =
  let rt = andD_keep b in
  clear b;
  rt

(* proof as lambda term *)

let lbd_exact : term -> Tac unit =
  t_exact false true


(* description of the transformation *)

type usq_t : Type =
  | Nop : usq_t
  | All : usq_t -> usq_t
  | Imp : usq_t -> usq_t -> usq_t
  | And : usq_t -> usq_t -> usq_t

let iff (p0 p1 : usq_t) : usq_t
  = And (Imp p0 p1) (Imp p1 p0)

let rec usq_t_of_term (f:term) : Tac usq_t =
  match F.term_as_formula_total f with
  | F.Forall _ t    -> All (usq_t_of_term t)
  | F.Implies t0 t1 -> Imp (usq_t_of_term t0) (usq_t_of_term t1)
  | F.And     t0 t1 -> And (usq_t_of_term t0) (usq_t_of_term t1)
  | _ -> Nop

(* TODO: equivalent of Coq's `;` instead of CPS *) 
let rec unsquash_goal (d : usq_t) (ct : unit -> Tac unit) : Tac unit
  = match d with
    | Nop   -> ct ()
    | All d ->
          let x = allI () in
          unsquash_goal d (fun () ->
            revert (); (* x *)
            ct ())
    | Imp dh dg ->
          let h = impI () in
          unsquash_goal dg (fun () ->
            unsquash_hyp dh h;
            ct ())
    | And dl dr ->
          andI ();
          iseq [(fun () -> unsquash_goal dl ct); (fun () -> unsquash_goal dr ct)]
(* revert the transformed hypothesis *)
and unsquash_hyp (d : usq_t) (h : binder) : Tac unit
  = match d with
    | Nop ->
          revert () (* h *)
    | All Nop ->
          let h = allD h in
          revert () (* h *)
    | All _ ->
          fail "AllD _ : Not implemented"
    | Imp Nop Nop ->
          let h = impD h in
          revert () (* h *)
    | Imp _ _ ->
          fail "ImpD _ _ : Not implemented"
    | And dl dr ->
          let hl,hr = andD h in
          unsquash_hyp dr hr;
          unsquash_hyp dl hl

let usq (d : usq_t) : Tac unit = unsquash_goal d (fun () -> ())

let rec iter_list (#a : Type) (f : a -> Tac unit) (l : list a) : Tac unit =
  match l with
  | [] -> ()
  | hd :: tl -> f hd; iter_list f tl

let lbd_prf (d : usq_t) (pfs : list term) : Tac unit
  = usq d;
    iter_list lbd_exact pfs
