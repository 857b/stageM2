module Learn.Steel.List.Derived

let v (#a:Type) (entry : ref (cell a)) (len : nat)
  = mlist #a entry len null

let f (#a:Type) (entry : ref (cell a)) (len : nat) (l : t_of (v entry len)) : mlistN_sel_t #a entry
  = l

let mlistN_sl #a (entry : ref (cell a)) =
  US.vexists_sl (v #a entry)

let mlistN_indep #a (entry : ref (cell a))
  : Lemma (ensures US.vexists_indep (v entry) #(mlistN_sel_t entry) (f entry))
  = US.vexists_indepI_unique (v entry) (mlistN_length_unique entry)

let mlistN_sel #a (entry : ref (cell a)) =
  mlistN_indep entry;
  US.vexists_sel (v #a entry) #(mlistN_sel_t entry) (f #a entry)

let intro_mlistN #a #opened entry len =
  mlistN_indep entry;
  US.intro_vexists len (v entry) #(mlistN_sel_t entry) (f entry)

let elim_mlistN (#a:Type) (#opened:inames) (entry:ref (cell a))
  =
    mlistN_indep entry;
    US.witness_vexists #nat (v entry) #(mlistN_sel_t entry) (f entry)
