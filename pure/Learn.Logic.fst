module Learn.Logic

let forall_morph_iff (#a : Type) (p0 p1 : a -> prop)
      (prf : (x : a) -> Lemma (p0 x <==> p1 x))
  : Lemma ((forall (x : a) . p0 x) <==> (forall (x : a) . p1 x))
  = FStar.Classical.forall_intro prf

let exists_morph_iff (#a : Type) (p0 p1 : a -> prop)
      (prf : (x : a) -> Lemma (p0 x <==> p1 x))
  : Lemma ((exists (x : a) . p0 x) <==> (exists (x : a) . p1 x))
  = FStar.Classical.forall_intro prf

let wp_morph_iff (#a : Type) (wp : pure_wp a) (pt0 pt1 : pure_post a)
      (prf : (x : a) -> Lemma (pt0 x <==> pt1 x))
  : Lemma (ensures wp pt0 <==> wp pt1)
  = FStar.Classical.forall_intro prf;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp
