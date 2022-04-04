module Learn.Tactics.Unsquash

module F = FStar.Reflection.Formula

open FStar.Tactics

private
let __pose (goal:Type) (#t:Type) (x : t) (f : t -> goal) : goal = f x

let pose' (t:term) : Tac binder =
    apply (`__pose (`#(cur_goal ())));
    exact t;
    intro ()


(* [allI] : introduces [forall (x : t) . p x] with [x:t |- squash (p x)] *)

let allI : unit -> Tac binder = forall_intro

(* [allD] : destructs [forall (x : t) . p x] into [(x : t) -> squash (p x)] *)

private
let __allD #t (#pred : t -> Type0) (h : (forall x. pred x)) : x:t -> squash (pred x) =
  fun x -> ()

private
let __allD_sq #t (#pred : t -> Type0) (h : squash (forall x. pred x)) : x:t -> squash (pred x) =
  fun x -> ()

let allD_keep (fa : term) : Tac binder =
  try pose' (`__allD_sq (`#fa)) with | _ ->
  try pose' (`__allD    (`#fa)) with | _ ->
  fail "allD: could not unsquash"

let allD (fa : binder) : Tac binder =
  let faa = allD_keep fa in
  clear fa;
  faa


(* [impI] : introduces [a ==> b] with [_ : squash a |- squash b] *)

private let __impI (#a #b:Type) (prf : squash a -> squash b) : Lemma (a ==> b)
  = introduce a ==> b with pf_a . prf pf_a

let impI () : Tac binder =
  apply_lemma (`__impI);
  intro ()

(* [impD] : destructs [a ==> b] into [squash a -> squash b] *)

private
let __impD (#a #b : Type) (h : (a ==> b)) : squash a -> squash b =
  fun pa -> ()

private
let __impD_sq (#a #b : Type) (h : squash (a ==> b)) : squash a -> squash b =
  fun pa -> ()

let impD_keep (ip : term) : Tac binder =
  try pose' (`__impD_sq (`#ip)) with | _ ->
  try pose' (`__impD    (`#ip)) with | _ ->
  fail "impD: could not unsquash"

let impD (ip : binder) : Tac binder =
  let rt = impD_keep ip in
  clear ip;
  rt


(* [andI] : introduces [a /\ b] with [squash a] and [squash b] *)

let andI : unit -> Tac unit = split

(* [andI1] : introduces [a /\ b] with [(squash a) & (squash b)] *)

private let __andI1 (#a #b:Type) (prf : (squash a) & (squash b)) : Lemma (a /\ b)
  = ()

let andI1 () : Tac unit =
  apply_lemma (`__andI1)

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

(* [andD1] : destrucs [a /\ b] into [(squash a) & (squash b)] *)

private
let __andD1 (#a #b : Type) (h : (a /\ b)) : (squash a) & (squash b) =
  (), ()

private
let __andD1_sq (#a #b : Type) (h : squash (a /\ b)) : (squash a) & (squash b) =
  (), ()

let andD1_keep (cj : term) : Tac binder =
  try pose' (`__andD1_sq (`#cj)) with | _ ->
  try pose' (`__andD1    (`#cj)) with | _ ->
  fail "andD1: could not unsquash"

let andD1 (cj : binder) : Tac binder =
  let rt = andD1_keep cj in
  clear cj;
  rt


(* [->] is a morphism in its target *)

private
let __hyp_arrow_morph_right (goal : Type) (#t : Type) (#p : t -> Type) (#q : t -> Type) (h : (x:t) -> p x)
                            (f : (x:t) -> p x -> q x) (ct : ((x:t) -> q x) -> goal) : goal
  = ct (fun x -> f x (h x)) 

let hyp_arrow_morph_right
    (f : binder(*x:t*) -> binder(*p x*) -> Tac binder(*q x*))
    (ar : binder(*x:t -> p x*))
  : Tac binder(*x:t -> q x*) =
  apply (`__hyp_arrow_morph_right (`#(cur_goal ())) (`#ar));
  begin let x = intro ()  in
        let p = intro ()  in
        let q = f x p in
        exact q
  end;
  clear ar;
  let ar = intro () in
  norm_binder_type [] ar;
  ar


(* [&] is a morphism *)

private
let __goal_pair_morph (#p0 #p1 #q0 #q1 : Type) (f0 : p0 -> q0) (f1 : p1 -> q1) (x : p0 & p1) : q0 & q1
  = (f0 x._1, f1 x._2)

let goal_pair_morph (f0 : unit -> Tac unit(*q0 <- p0*)) (f1 : unit -> Tac unit(*q1 <- p1*))
  : Tac unit(*q0&q1 <- p0&p1*)
  = apply (`__goal_pair_morph);
    begin let p0 = intro () in
          f0 ();
          exact p0
    end;
    begin let p1 = intro () in
          f1 ();
          exact p1
    end

private
let __hyp_pair_morph (goal : Type) (#p0 #p1 #q0 #q1 : Type) (h : p0 & p1)
                     (f0 : p0 -> q0) (f1 : p1 -> q1) (ct : (q0 & q1) -> goal) : goal
  = ct (f0 h._1, f1 h._2)

let hyp_pair_morph
    (f0 : binder(*p0*) -> Tac binder(*q0*)) (f1 : binder(*p1*) -> Tac binder(*q1*))
    (pr : binder(*p0&p1*))
  : Tac binder(*q0&q1*) =
  apply (`__hyp_pair_morph (`#(cur_goal ())) (`#pr));
  begin let p0 = intro ()  in
        let q0 = f0 p0 in
        exact q0
  end;
  begin let p1 = intro ()  in
        let q1 = f1 p1 in
        exact q1
  end;
  clear pr;
  intro ()
           

(* proof by a lambda term *)

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
(* [sg] : split goal
   [sh] : split hypotheses *)
let rec unsquash_goal (sg : bool) (sh : bool) (d : usq_t) (ct : unit -> Tac unit) : Tac unit
  = match d with
    | Nop   -> ct ()
    | All d ->
          let x = allI () in
          unsquash_goal sg sh d (fun () ->
            revert (); (* x *)
            ct ())
    | Imp dh dg ->
          let h = impI () in
          unsquash_goal sg sh dg (fun () ->
            unsquash_hyp sh dh h;
            ct ())
    | And dl dr ->
          if sg then begin
            andI ();
            iseq [(fun () -> unsquash_goal sg sh dl ct);
                  (fun () -> unsquash_goal sg sh dr ct)]
          end else begin
            andI1 ();
            goal_pair_morph (fun () -> unsquash_goal false sh dl (fun () -> ()))
                            (fun () -> unsquash_goal false sh dr (fun () -> ()));
            ct ()
          end

(* revert the transformed hypothesis (which may be split into several hypotheses) *)
and unsquash_hyp (sh : bool) (d : usq_t) (h : binder) : Tac unit
  = let rev1 () : Tac unit =
       let h = unsquash_hyp1 d h in
       revert () (* h *)
    in
    if not sh then rev1 ()
    else match d with
    | Nop | All _ | Imp _ _ -> rev1 ()
    | And dl dr ->
          let hl,hr = andD h in
          unsquash_hyp sh dr hr;
          unsquash_hyp sh dl hl
          
(* return the transformed hypothesis *)
and unsquash_hyp1 (d : usq_t) (h : binder) : Tac binder
   = match d with
    | Nop ->
          h
    | All d ->
          let h = allD h in
          hyp_arrow_morph_right (fun x p -> unsquash_hyp1 d p) h
    | Imp Nop dr ->
          let h = impD h in
          hyp_arrow_morph_right (fun _ p -> unsquash_hyp1 dr p) h
    | Imp _ _ ->
          fail "ImpD _ _ : Not implemented"
    | And dl dr ->
          let h = andD1 h in
          hyp_pair_morph (unsquash_hyp1 dl) (unsquash_hyp1 dr) h


let usq (split_goal split_hyps : bool) (d : usq_t) : Tac unit
  = unsquash_goal split_goal split_hyps d (fun () -> ())

(* Representation of [usq_t] with [term] *)

(* from FSTAR_HOME/examples/tactics/Preprocess.fst *)
let is_fv (fv:string) (t:term) : Tac bool =
  match t with
  | Tv_FVar fv' ->
    String.concat "." (inspect_fv fv') = fv
  | _ -> false

let rec term_to_usq_t (t : term) : Tac usq_t =
  match inspect_ln t with
  | Tv_App _ _ ->
    begin match collect_app t with
    | h, [arg0, Q_Explicit] ->
           if is_fv (`%Prims.l_Forall) h then
             let t' = match inspect_ln arg0 with
                      | Tv_Abs _ t' -> t' | _ -> fail "term_to_usq_t.0"
             in
             All (term_to_usq_t t')
           else fail "term_to_usq_t.1"
    | h, [arg0, Q_Explicit; arg1, Q_Explicit] ->
           if is_fv (`%Prims.l_imp) h then
             Imp (term_to_usq_t arg0) (term_to_usq_t arg1)
           else if is_fv (`%Prims.l_and) h then
             And (term_to_usq_t arg0) (term_to_usq_t arg1)
           else if is_fv (`%Prims.l_iff) h then
             iff (term_to_usq_t arg0) (term_to_usq_t arg1)
           else fail ("term_to_usq_t.2: "^term_to_string (quote h))
    | h,args ->  fail ("term_to_usq_t.3: "^term_to_string (quote h)^"   "^term_to_string (quote args))
    end
  | Tv_Unknown -> Nop
  | _ -> fail "term_to_usq_t.4"


(*let () = assert True by (let d = term_to_usq_t (`(_ <==> _)) in print (term_to_string (quote d)); smt ()) *)

let lbd_prf (d : term) (pf : term) : Tac unit
  = usq false true (term_to_usq_t d);
    lbd_exact pf

let rec iter_list (#a : Type) (f : a -> Tac unit) (l : list a) : Tac unit =
  match l with
  | [] -> ()
  | hd :: tl -> f hd; iter_list f tl

let lbd_prfs (d : term) (pfs : list term) : Tac unit
  = usq true true (term_to_usq_t d);
    iter_list lbd_exact pfs
