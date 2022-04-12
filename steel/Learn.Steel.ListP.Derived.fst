module Learn.Steel.ListP.Derived

let v (p : list_param) (entry : ref p.r) (len : nat)
  = mlist p entry len null

let f (p : list_param) (entry : ref p.r) (len : nat) (l : t_of (v p entry len)) : mlistN_sel_t p entry
  = l

let mlistN_sl (p : list_param) (entry : ref p.r) =
  US.vexists_sl (v p entry)

let mlistN_indep (p : list_param) (entry : ref p.r)
  : Lemma (ensures US.vexists_indep (v p entry) (f p entry))
  = US.vexists_indepI_unique (v p entry) (mlistN_length_unique p entry)

let mlistN_sel (p : list_param) (entry : ref p.r) =
  mlistN_indep p entry;
  US.vexists_sel (v p entry) (f p entry)

let intro_mlistN #opened (p : list_param) entry len =
  mlistN_indep p entry;
  US.intro_vexists len (v p entry) (f p entry)

let elim_mlistN #opened (p : list_param) entry
  =
    mlistN_indep p entry;
    US.witness_vexists (v p entry) (f p entry)
