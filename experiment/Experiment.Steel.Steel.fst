module Experiment.Steel.Steel

module T    = FStar.Tactics
module Fext = FStar.FunctionalExtensionality


let rmem_star_eq (#p : vprop) (v0 v1 : vprop) (h : rmem p{can_be_split p (VStar v0 v1)})
  : Lemma (can_be_split p v0 /\ can_be_split p v1 /\
           h (VStar v0 v1) == (h v0, h v1))
  =
    can_be_split_star_l v0 v1;
    can_be_split_star_r v0 v1;
    can_be_split_trans p (VStar v0 v1) v0;
    can_be_split_trans p (VStar v0 v1) v1;
    // TODO: this is implied by [valid_rmem] but not exposed by the interface of [Steel.Effect.Common]
    //       maybe we can do the proofs in SteelGhost
    admit ()

(*** Steel *)

let focus_rmem_feq (p q r : vprop) (h : rmem p)
  : Lemma (requires can_be_split p q /\ can_be_split q r)
          (ensures  can_be_split p r /\ focus_rmem h q r == h r)
  = can_be_split_trans p q r

let focus_rmem_trans (p q r : vprop) (h : rmem p)
  : Lemma (requires can_be_split p q /\ can_be_split q r)
          (ensures  can_be_split p r /\ focus_rmem (focus_rmem h q) r == focus_rmem h r)
  = can_be_split_trans p q r;
    introduce forall (r0 : vprop {can_be_split r r0}) .
        (focus_rmem (focus_rmem h q) r) r0 == (focus_rmem h r) r0
      with _ by T.(trefl ());
    Fext.extensionality_g _ _ (focus_rmem (focus_rmem h q) r) (focus_rmem h r)


let intro_subcomp_no_frame_pre
      (#a:Type)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
      (s_pre :  (h0 : rmem pre_g) -> Lemma
         (requires can_be_split pre_g pre_f /\
                   req_g h0)
         (ensures  req_f (focus_rmem h0 pre_f)))
      (s_post : (h0 : rmem pre_g) -> (x : a) -> (h1 : rmem (post_g x)) -> Lemma
         (requires can_be_split pre_g pre_f /\ can_be_split (post_g x) (post_f x) /\
                   req_g h0 /\ req_f (focus_rmem h0 pre_f) /\
                   ens_f (focus_rmem h0 pre_f) x (focus_rmem h1 (post_f x)))
         (ensures  ens_g h0 x h1))
  : squash (subcomp_no_frame_pre req_f ens_f req_g ens_g eq_pre eq_post)
  = _ by T.(
    set_guard_policy Force;
    norm [delta_only [`%subcomp_no_frame_pre]];
    let h0   = forall_intro () in
    let rq_g = implies_intro () in
    split ();
    
    apply_lemma (``@s_pre); split ();
      apply_lemma (`equiv_can_be_split); exact (``@eq_pre);
      hyp rq_g;

    let x    = forall_intro ()  in
    let h1   = forall_intro ()  in
    let en_f = implies_intro () in
    apply_lemma (``@s_post); explode ();
      apply_lemma (`equiv_can_be_split); exact (``@eq_pre);
      apply_lemma (`equiv_can_be_split); apply (``@eq_post);
      hyp rq_g;
      apply_lemma (``@s_pre); split ();
        apply_lemma (`equiv_can_be_split); exact (``@eq_pre);
        hyp rq_g;
      hyp en_f
  )

let subcomp_no_frame_lem
      (#a : Type)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
  : Lemma (can_be_split pre_g (pre_f `star` emp) /\ equiv_forall post_g (fun x -> post_f x `star` emp))
  =
    equiv_can_be_split pre_g pre_f;
    assert (can_be_split pre_f (pre_f `star` emp) /\ True)
      by (T.squash_intro (); selector_tactic ());
    can_be_split_trans pre_g pre_f (pre_f `star` emp);

    introduce forall (x : a) . post_g x `equiv` (post_f x `star` emp)
    with (
      eq_post x;
      assert (post_f x `equiv` (post_f x `star` emp))
        by (init_resolve_tac ());
      equiv_trans (post_g x) (post_f x) (post_f x `star` emp)
    );
    equiv_forall_elim post_g (fun x -> post_f x `star` emp)

inline_for_extraction noextract
let unit_steel_subcomp_no_frame
      (#a : Type)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
      (sb_pre : squash (subcomp_no_frame_pre req_f ens_f req_g ens_g eq_pre eq_post))
      (f : unit_steel a pre_f post_f req_f ens_f)
  : unit_steel a pre_g post_g req_g ens_g
  =
    subcomp_no_frame_lem req_f ens_f req_g ens_g eq_pre eq_post;
    intro_subcomp_pre' req_f ens_f req_g ens_g #emp #True () ()
      (fun h0 -> ()) (fun h0 -> ()) (fun h0 x h1 -> ());
    steel_subcomp a
      pre_f post_f req_f ens_f
      pre_g post_g req_g ens_g
      emp True () () ()
      f

inline_for_extraction noextract
let unit_steel_ghost_subcomp_no_frame
      #a #opened
      #pre_f #post_f req_f ens_f
      #pre_g #post_g req_g ens_g
      eq_pre eq_post sb_pre f
  =
    subcomp_no_frame_lem req_f ens_f req_g ens_g eq_pre eq_post;
    intro_subcomp_pre' req_f ens_f req_g ens_g #emp #True () ()
      (fun h0 -> ()) (fun h0 -> ()) (fun h0 x h1 -> ());
    steel_ghost_subcomp a opened
      pre_f post_f req_f ens_f
      pre_g post_g req_g ens_g
      emp True () () ()
      f
