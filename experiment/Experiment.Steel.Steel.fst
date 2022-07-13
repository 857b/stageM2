module Experiment.Steel.Steel

module T    = FStar.Tactics
module Fext = FStar.FunctionalExtensionality


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

let focus_rmem_mkrmem (p q : vprop) (h : hmem p)
  : Lemma (requires can_be_split p q)
          (ensures  Mem.interp (hp_of q) h /\ focus_rmem (mk_rmem p h) q == mk_rmem q h)
  =
    can_be_split_interp p q h;
    introduce forall (r : vprop {can_be_split q r}) .
        (focus_rmem (mk_rmem p h) q) r == (mk_rmem q h) r
      with _ by T.(trefl ());
    Fext.extensionality_g _ _ (focus_rmem (mk_rmem p h) q) (mk_rmem q h)

let intro_subcomp_no_frame_pre0
      (#a:Type)
      (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
      (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
      (eq_pre  : squash (equiv pre_g pre_f))
      (eq_post : (x : a) -> squash (equiv (post_g x) (post_f x)))
      (s_pre :  (h0 : hmem pre_g) -> Lemma
         (requires can_be_split pre_g pre_f /\
                   req_g (mk_rmem pre_g h0))
         (ensures  req_f (focus_rmem (mk_rmem pre_g h0) pre_f)))
      (s_post : (h0 : hmem pre_g) -> (x : a) -> (h1 : hmem (post_g x)) -> Lemma
         (requires can_be_split pre_g pre_f /\ can_be_split (post_g x) (post_f x) /\
                   req_g (mk_rmem pre_g h0) /\ req_f (focus_rmem (mk_rmem pre_g h0) pre_f) /\
                   ens_f (focus_rmem (mk_rmem pre_g h0) pre_f) x (focus_rmem (mk_rmem (post_g x) h1) (post_f x)))
         (ensures  ens_g (mk_rmem pre_g h0) x (mk_rmem (post_g x) h1))) 
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

let intro_subcomp_no_frame_pre
      #a #pre_f #post_f req_f ens_f #pre_g #post_g req_g ens_g
      eq_pre eq_post s_pre s_post
  =
    intro_subcomp_no_frame_pre0 req_f ens_f req_g ens_g eq_pre eq_post
      (fun h0      -> focus_rmem_mkrmem pre_g pre_f h0;
                   s_pre h0)
      (fun h0 x h1 -> focus_rmem_mkrmem pre_g pre_f h0;
                   focus_rmem_mkrmem (post_g x) (post_f x) h1;
                   s_post h0 x h1)


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
