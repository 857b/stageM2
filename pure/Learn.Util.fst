module Learn.Util

(* TODO? [@opaque_to_smt] *)
let hide_prop p = p

let hide_propI p = ()

let hide_propI_by p prf = prf ()

let hide_propD p = ()

let f_equal #a #b f x y = ()

let prop_equal #a p x y = ()

let assert_by p prf = prf ()


module T = FStar.Tactics

(* from F* tutorial *)
let funext_on_eta (#a : Type) (#b: a -> Type) (f g : (x:a -> b x))
                  (hp : (x:a -> squash (f x == g x)))
  : squash (eta f == eta g)
  = _ by T.(norm [delta_only [`%eta]];
          pointwise (fun _ ->
             try_with
                     (fun _ -> mapply (quote hp))
                     (fun _ -> trefl()));
           trefl())

let funext_on_eta_gtot (#a : Type) (#b: a -> Type) (f g : (x:a -> GTot (b x)))
                  (hp : (x:a -> squash (f x == g x)))
  : squash (eta_gtot f == eta_gtot g)
  = _ by T.(norm [delta_only [`%eta_gtot]];
          pointwise (fun _ ->
             try_with
                     (fun _ -> mapply (quote hp))
                     (fun _ -> trefl()));
           trefl())

let arrow_ext
      (#a : Type) (f g : a -> Type)
      (pf : (x : a) -> squash (f x == g x))
  : squash (((x : a) -> f x) == ((x : a) -> g x))
  =
    calc (==) {
      (x : a) -> f x;
    == { _ by (T.trefl ()) }
      (x : a) -> (eta f) x;
    == { funext_on_eta f g pf;
         f_equal (fun f -> (x : a) -> f x) (eta f) (eta g) }
      (x : a) -> (eta g) x;
    == { _ by (T.trefl ()) }
      (x : a) -> g x;
    }
