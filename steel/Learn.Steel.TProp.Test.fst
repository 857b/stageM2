module Learn.Steel.TProp.Test

module T = FStar.Tactics

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Reference
open Learn.Steel.TProp

let vptr_opt_tp (#a : Type) (rb : ghost_ref bool) (rx : ref a) : tprop (option a)
  =
    b <-- vpr (ghost_vptr rb);
    if b
    then begin
      x <-- vprt a (vptr rx);
      return (Some x)
    end else
      return None

let vptr_opt (#a : Type) (rb : ghost_ref bool) (rx : ref a) : vprop
  = vprop_of_tprop (vptr_opt_tp rb rx)

let intro_vptr_opt_Some #a rb rx (m : mem)
      (_ : squash (interp (hp_of (ghost_vptr rb `star` vptr rx)) m /\
                   b2t (sel_of (ghost_vptr rb) m)))
  : squash (interp (hp_of (vptr_opt rb rx)) m /\
            sel_of (vptr_opt rb rx) m == Some (sel_of (vptr rx) m))
  = _ by T.(
    let _ =
      pose_interp_lemma (`vptr_opt_tp (`@rb) (`@rx)) (``@m)
        (fun () -> norm [delta_only [`%vptr_opt_tp]])
        [1]
    in smt ())

let elim_vptr_opt #a (rb : ghost_ref bool) (rx : ref a) (m : mem)
  : Lemma (requires interp (hp_of (vptr_opt rb rx)) m)
          (ensures  interp (hp_of (ghost_vptr rb)) m /\
                    (if coerce_eq _ (sel_of (ghost_vptr rb) m)
                     then interp (hp_of (ghost_vptr rb `star` vptr rx)) m /\
                          sel_of (vptr_opt rb rx) m == Some (sel_of (vptr rx) m)
                     else sel_of (vptr_opt rb rx) m == None #a))
  =
    let tp  = vptr_opt_tp rb rx in
    let rew () = T.norm [delta_only [`%vptr_opt_tp]] in
    assert (interp (hp_of (ghost_vptr rb)) m)
      by T.(let _ = pose_interp_lemma (`(`@tp)) (``@m) rew [0] in smt ());
    if coerce_eq _ (sel_of (ghost_vptr rb) m)
    then assert (interp (hp_of (ghost_vptr rb `star` vptr rx)) m /\
                 sel_of (vptr_opt rb rx) m == Some (sel_of (vptr rx) m))
           by T.(let _ = pose_interp_lemma (`(`@tp)) (``@m) rew [1] in smt ())
    else assert (sel_of (vptr_opt rb rx) m == None #a)
           by T.(let _ = pose_interp_lemma (`(`@tp)) (``@m) rew [2] in smt ())
