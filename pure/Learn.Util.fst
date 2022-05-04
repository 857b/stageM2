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
                  (hp : (x:a -> Lemma (f x == g x)))
  : squash (eta f == eta g)
  = _ by T.(norm [delta_only [`%eta]];
          pointwise (fun _ ->
             try_with
                     (fun _ -> mapply (quote hp))
                     (fun _ -> trefl()));
           trefl())
