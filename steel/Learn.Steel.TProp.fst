module Learn.Steel.TProp

#set-options "--fuel 1 --ifuel 1"

let interp_of_opt (slp : option slprop) (m : mem)
  = Mem.intro_emp m

let star_of_opt (slp0 slp1 : option slprop)
  = match slp0 with
    | None      -> Mem.star_commutative Mem.emp (slprop_of_opt slp1); Mem.emp_unit (slprop_of_opt slp1)
    | Some slp0 ->
    match slp1 with
    | None      -> Mem.emp_unit slp0
    | Some slp1 -> ()

let interp_star_opt (slp0 slp1 : option slprop) (m : mem)
  = calc (<==>) {
    interp_opt (star_opt slp0 slp1) m;
  <==> { interp_of_opt (star_opt slp0 slp1) m;
       star_of_opt slp0 slp1 }
    interp (slprop_of_opt slp0 `Mem.star` slprop_of_opt slp1) m;
  <==> { Mem.interp_star (slprop_of_opt slp0) (slprop_of_opt slp1) m }
    exists (m0 m1 : mem) . disjoint m0 m1 /\ join m0 m1 == m /\
                      interp (slprop_of_opt slp0) m0 /\ interp (slprop_of_opt slp1) m1;
  <==> { FStar.Classical.forall_intro (interp_of_opt slp0);
       FStar.Classical.forall_intro (interp_of_opt slp1) }
    exists (m0 m1 : mem) . disjoint m0 m1 /\ join m0 m1 == m /\
                      interp_opt slp0 m0 /\ interp_opt slp1 m1;
  }


let tprop_interp_intro
      #t u guard req slp sel
      (int_sl : (m : mem) -> squash (guard m) ->
                squash (interp u.t_hp m <==> req m /\ interp_opt (slp m) m))
      (sel_eq : (m : Mem.hmem u.t_hp) -> squash (guard m /\ req m /\ interp_opt (slp m) m) ->
                squash (u.t_sel m == sel m))
      (join0  : (m0:mem{guard m0 /\ req m0}) -> (m1:mem{disjoint m0 m1}) ->
                   squash (let m = join m0 m1 in guard m /\ req m /\ slp m == slp m0 /\ sel m == sel m0))
      (join1  : (m0:mem) -> (m1:mem{disjoint m0 m1}) ->
                   squash (let m = join m0 m1 in guard m /\ req m /\ (interp u.t_hp m0 \/ interp_opt (slp m) m0)) ->
                   squash (guard m0 /\ req m0))
  : tprop_interp u guard req slp sel
  = {
    tpi_int_sl =
      introduce forall (m : mem {guard m}) . (interp u.t_hp m <==> req m /\ interp_opt (slp m) m)
        with int_sl m ();
    tpi_sel_eq =
      introduce forall (m : Mem.hmem u.t_hp {guard m /\ req m}) . u.t_sel m == sel m
        with (int_sl m (); sel_eq m ());
    tpi_join0 =
      introduce forall (m0: mem{guard m0 /\ req m0}) (m1:mem{disjoint m0 m1}) .
                guard (join m0 m1) /\ req (join m0 m1) /\ slp (join m0 m1) == slp m0 /\ sel (join m0 m1) == sel m0
        with join0 m0 m1;
    tpi_join1 =
      introduce forall (m0:mem) (m1:mem{disjoint m0 m1}) .
                (guard (join m0 m1) /\ req (join m0 m1) /\
                  (interp u.t_hp m0 \/ interp_opt (slp (join m0 m1)) m0)) ==>
                (guard m0 /\ req m0)
        with introduce _ ==> _ with _ . join1 m0 m1 ();
  }

let tprop_interp_elim
      #t #u #guard #req #slp #sel tpi
      (m : mem)
  = tpi.tpi_int_sl; tpi.tpi_sel_eq

let tprop_interp_join0
      #t (#u : tprop t) #guard #req #slp #sel (tpi : tprop_interp u guard req slp sel)
      (m0 m1 : mem)
  : Lemma (requires disjoint m0 m1 /\ guard m0)
          (ensures (let m = join m0 m1 in
                    req m0 ==> (guard m /\ req m /\ slp m == slp m0 /\ sel m == sel m0)))
  = tpi.tpi_join0

let tprop_interp_join1
      #t (#u : tprop t) #guard #req #slp #sel (tpi : tprop_interp u guard req slp sel)
      (m0 m1 : mem)
  : Lemma (requires disjoint m0 m1)
          (ensures  (guard (join m0 m1) /\ req (join m0 m1) /\
                      (interp u.t_hp m0 \/ interp_opt (slp (join m0 m1)) m0)) ==>
                    (guard m0 /\ req m0))
  = tpi.tpi_join1


let tprop_trivial_interp (#t : Type) (u : tprop t)
  = tprop_interp_intro _ _ _ _ _
      (fun m _ -> ()) (fun m _ -> ()) (fun m0 m1 -> ()) (fun m0 m1 _ -> ())

let tprop_of_vprop_interp (t : Type) (v : vprop {normal (t_of v) == t})
  = tprop_interp_intro _ _ _ _ _
      (fun m _ -> ()) (fun m _ -> ()) (fun m0 m1 -> ()) (fun m0 m1 _ -> ())


(***** [treturn] *)

let treturn_sel (#a : Type) (x : erased a) : selector a Mem.emp
  =
    let sel' (_ : Mem.hmem Mem.emp) : GTot a = x in
    sel'

let treturn (#a : Type) (x : erased a) : tprop a
  = {
    t_hp  = Mem.emp;
    t_sel = treturn_sel x;
  }

let treturn_int_sl (#a : Type) (x : erased a) (m : mem)
  = Mem.intro_emp m

let treturn_sel_eq (#a : Type) (x : erased a) (m : mem)
  = ()

let treturn_interp (#a : Type) (x : erased a)
  = tprop_interp_intro _ _ _ _ _
      (fun m _ -> Mem.intro_emp m) (fun m _ -> ()) (fun m0 m1 -> ()) (fun m0 m1 _ -> ())


(***** [tbind] *)

let tbind_vdep_rhs (#a #b : Type) (v : a -> tprop b) (x : a) : vprop
  =
    vprop_of_tprop (v x)

let tbind_vprop (#a #b : Type) (u : tprop a) (v : a -> tprop b) : vprop
  =
    vrewrite (vprop_of_tprop u `vdep` tbind_vdep_rhs v) #b Mkdtuple2?._2

let tbind (#a #b : Type) (u : tprop a) (v : a -> tprop b) : tprop b
  =
    tprop_of_vprop b (tbind_vprop u v)

let tbind_int_sl (#a #b : Type) (u : tprop a) (v : a -> tprop b) (m : mem)
  = interp_vdep_hp (vprop_of_tprop u) (tbind_vdep_rhs v) m

let tbind_sel_eq (#a #b : Type) (u : tprop a) (v : a -> tprop b) (m : Mem.hmem (tbind u v).t_hp)
  = tbind_int_sl u v m;
    vrewrite_sel_eq (vprop_of_tprop u `vdep` tbind_vdep_rhs v) #b Mkdtuple2?._2 m;
    vdep_sel_eq (vprop_of_tprop u) (tbind_vdep_rhs v) m

let tbind_interp
      #a #b u v
      #u_guard #u_req #u_slp #u_sel u_tpi
      #v_guard #v_req #v_slp #v_sel v_tpi
  = tprop_interp_intro _ _ _ _ _
    begin fun m _ ->
      introduce interp (tbind u v).t_hp m ==> u_req m /\ v_req (u_sel m) m
        with _ . (tbind_int_sl u v m; tprop_interp_elim u_tpi m; tprop_interp_elim (v_tpi (u_sel m)) m);
      introduce u_req m /\ v_req (u_sel m) m ==>
                (interp (tbind u v).t_hp m <==>
                  (v_req (u_sel m) m /\ interp_opt (u_slp m `star_opt` v_slp (u_sel m) m) m))
        with _ . begin
        let x = u_sel m in
        assert (u_guard m /\ (u_req m ==> v_guard x m));
        calc (<==>) {
          interp (tbind u v).t_hp m;
        <==> { tbind_int_sl u v m }
          interp u.t_hp m /\ interp (u.t_hp `Mem.star` (v (u.t_sel m)).t_hp) m;
        <==> { tprop_interp_elim u_tpi m }
          interp (u.t_hp `Mem.star` (v x).t_hp) m;
        <==> { interp_star u.t_hp (v x).t_hp m }
          exists (m0 m1 : mem) .
            disjoint m0 m1 /\ join m0 m1 == m /\ interp u.t_hp m0 /\ interp (v x).t_hp m1;
        <==> { let lem (m0 m1 : mem)
               : Lemma (requires disjoint m0 m1 /\ join m0 m1 == m)
                       (ensures  (interp u.t_hp     m0 <==> interp_opt (u_slp m)   m0) /\
                                 (interp (v x).t_hp m1 <==> interp_opt (v_slp x m) m1))
                       [SMTPat (disjoint m0 m1)]
               =
                 introduce (interp u.t_hp m0 \/ interp_opt (u_slp m) m0) ==>
                           (interp u.t_hp m0 /\ interp_opt (u_slp m) m0)
                   with _ . begin
                     tprop_interp_join1 u_tpi m0 m1;
                     tprop_interp_elim  u_tpi m0;
                     tprop_interp_join0 u_tpi m0 m1
                   end;
                 introduce (interp (v x).t_hp m1 \/ interp_opt (v_slp x m) m1) ==>
                           (interp (v x).t_hp m1 /\ interp_opt (v_slp x m) m1)
                   with _ . begin
                     Mem.join_commutative m0 m1;
                     tprop_interp_join1 (v_tpi x) m1 m0;
                     tprop_interp_elim  (v_tpi x) m1;
                     tprop_interp_join0 (v_tpi x) m1 m0
                   end
             in ()
           }
          exists (m0 m1 : mem) .
            disjoint m0 m1 /\ join m0 m1 == m /\ interp_opt (u_slp m) m0 /\ interp_opt (v_slp x m) m1;
        <==> { interp_star_opt (u_slp m) (v_slp x m) m }
          interp_opt (u_slp m `star_opt` v_slp x m) m;
        }
        end
    end
    begin fun m _ ->
      tbind_int_sl u v m;
      tbind_sel_eq u v m;
      let x = u_sel m in
      tprop_interp_elim u_tpi m;
      calc (==) {
        (tbind u v).t_sel m;
      == { }
        (v (u.t_sel m)).t_sel m;
      == { }
        (v x).t_sel m;
      == { tprop_interp_elim (v_tpi x) m }
        v_sel x m;
      }
    end
    begin fun m0 m1 ->
      let m = join m0 m1 in
      assert (u_req m0 /\ v_req (u_sel m0) m0);
      tprop_interp_join0 u_tpi m0 m1;
      assert (u_req m /\ v_req (u_sel m) m0);
      tprop_interp_join0 (v_tpi (u_sel m)) m0 m1;
      assert (u_req m /\ v_req (u_sel m) m)
    end
    begin fun m0 m1 _ ->
      let m = join m0 m1 in
      let x = u_sel m    in
      assert (u_guard m /\ u_req m /\ v_guard x m /\ v_req x m);
      introduce interp (tbind u v).t_hp m0 ==> (interp u.t_hp m0 /\ interp (v x).t_hp m0)
        with _ . begin
          tbind_int_sl u v m0;
          tprop_interp_elim u_tpi m
        end;
      assert ((interp      u.t_hp   m0 /\ interp     (v x).t_hp  m0) \/
              (interp_opt (u_slp m) m0 /\ interp_opt (v_slp x m) m0));
      tprop_interp_join1  u_tpi    m0 m1;
      tprop_interp_join1 (v_tpi x) m0 m1;
      assert (u_req m0 /\ v_req x m0);
      tprop_interp_join0 u_tpi m0 m1;
      assert (u_req m0 /\ v_req (u_sel m0) m0)
    end


(***** [tpure] *)

let tpure_sel (p : Type0) : selector (squash p) (Mem.pure (p /\ True))
  =
    let sel' (m : Mem.hmem (Mem.pure (p /\ True))) : squash p = Mem.pure_interp (p /\ True) m in
    sel'

let tpure (p : Type0) : tprop (squash p)
  = {
    t_hp  = Mem.pure (p /\ True);
    t_sel = tpure_sel p
  }

let tpure_int_sl (p : Type0) (m : mem)
  = Mem.pure_interp (p /\ True) m

let tpure_sel_eq (p : Type0) (m : Mem.hmem (tpure p).t_hp)
  = tpure_int_sl p m

let tpure_interp (p : Type0)
  = tprop_interp_intro _ _ _ _ _
      (fun m _ -> tpure_int_sl p m) (fun m _ -> ()) (fun m0 m1 -> ()) (fun m0 m1 _ -> ())


(***** if-then-else *)

let ite_interp_then
      #a b thn els
      #guard #req #slp #sel tpi
  = tprop_interp_intro _ _ _ _ _
      (fun m _ -> tpi.tpi_int_sl) (fun m _ -> tpi.tpi_sel_eq) (fun m0 m1 -> tpi.tpi_join0) (fun m0 m1 _ -> tpi.tpi_join1)

let ite_interp_else
      #a b thn els
      #guard #req #slp #sel tpi
  = tprop_interp_intro _ _ _ _ _
      (fun m _ -> tpi.tpi_int_sl) (fun m _ -> tpi.tpi_sel_eq) (fun m0 m1 -> tpi.tpi_join0) (fun m0 m1 _ -> tpi.tpi_join1)
