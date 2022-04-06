module Learn.Util

(* TODO? [@opaque_to_smt] *)
let hide_prop p = p

let hide_propI p = ()

let hide_propI_by p prf = prf ()

let hide_propD p = ()

let f_equal #a #b f x y = ()

let prop_equal #a p x y = ()

let assert_by p prf = prf ()
