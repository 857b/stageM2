module Experiment.Steel.SteelHack

open FStar.Tactics

let intro_conj_with_impl (#a #b : Type0)
  : Lemma (requires a /\ (a ==> b)) (ensures a /\ b)
  = ()

let intro_subcomp_pre'
  (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (#frame:vprop)
  (#pr:prop)
  p1 p2 s_pr s_pre s_post
  : subcomp_pre' req_f ens_f req_g ens_g p1 p2
  = 
    let cbst_pre          = can_be_split_trans pre_g      (pre_f    `star` frame) in
    let cbst_post (x : a) = can_be_split_trans (post_g x) (post_f x `star` frame) in
    _ by (
    set_guard_policy Force;
    norm [delta_only [`%subcomp_pre']];
    split ();

    let h0   = forall_intro () in
    let rq_g = implies_intro () in
    apply_lemma (`intro_conj_with_impl); split ();
    apply_lemma (`(`@s_pr)); exact h0; hyp rq_g;
    let h_pr = implies_intro () in
    apply_lemma (`(`@s_pre)); explode ();
    hyp rq_g;
    hyp h_pr;
    apply_lemma (`(`@cbst_pre)); smt ();

    let h0 = forall_intro () in
    let x  = forall_intro () in
    let h1 = forall_intro () in
    let h_pr = implies_intro () in
    let _hs0  = implies_intro () in
    let _hs1,eq_fr  = destruct_and _hs0 in
    clear _hs0;
    let rq_g, en_f = destruct_and _hs1 in
    clear _hs1;
    apply_lemma (`(`@s_post));
    explode ();
    hyp rq_g;
    hyp h_pr;
    apply_lemma (`(`@cbst_pre)); smt ();
    apply_lemma (`(`@cbst_post)); smt ();
    apply_lemma (`can_be_split_interp); apply_lemma (`(`@cbst_pre));  smt ();
    apply_lemma (`can_be_split_interp); apply_lemma (`(`@cbst_post)); smt ();
    hyp en_f;
    hyp eq_fr
  )


/// Modified version of [init_resolve_tac]
[@@ resolve_implicits; framing_implicit; override_resolve_implicits_handler framing_implicit [`%init_resolve_tac]]
let resolve_framing () : Tac unit =
  let slgs, loggs = filter_goals (goals()) in
  set_goals slgs;
  solve_maybe_emps (List.Tot.length (goals ()));
  solve_indirection_eqs (List.Tot.length (goals()));

  //Solve the two goals using the hypothesis p1, p2
  let _ = repeatn 2 begin fun () ->
    first (map (fun (b : binder) -> fun () -> exact b <: Tac unit) (cur_binders ()))
  end in
  
  set_goals loggs;
  // Finally running the core of the tactic, scheduling and solving goals
  resolve_tac_logical []

let find_binder (nm : string) : Tac binder
  = first (map (fun (b : binder) () -> guard (term_to_string b = nm); b) (cur_binders ()))

[@@ handle_smt_goals ]
let tac () =
  let bs = cur_binders () in
  (try let so = find_binder "so" in
       split ();
       exact so
    with _ -> ());
  let sc = find_binder "sc" in
  norm_binder_type [delta_only [`%subcomp_pre']] sc;
  norm_binder_type normal_steps sc;
  exact sc

inline_for_extraction noextract
let steel_subcomp__steel a pre_f post_f req_f ens_f pre_g post_g req_g ens_g frame pr p1 p2 sc $f ()
  = f ()

inline_for_extraction noextract
let steel_subcomp__atomic o0 o1 a opened pre_f post_f req_f ens_f pre_g post_g req_g ens_g frame pr p1 p2 sc so $f ()
  = f ()

inline_for_extraction noextract
let steel_subcomp__ghost a opened pre_f post_f req_f ens_f pre_g post_g req_g ens_g frame pr p1 p2 sc $f ()
  = f ()
