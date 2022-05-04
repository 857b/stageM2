module Learn.ListFun

module U = Learn.Util
module T = FStar.Tactics

open FStar.List.Pure
open Learn.List


irreducible let __list_fun__ : unit = ()

/// The type [list_fun a b] is isomorphic to [list (a -> b)].

[@@ __list_fun__]
noeq type list_fun (a b : Type) = {
  lf_len  : nat;
  lf_list : a -> (l : list b {length l = lf_len});
}

unfold
let eta (#a #b : Type) (l : list_fun a b) : list_fun a b
  = {
    lf_len  = l.lf_len;
    lf_list = U.eta l.lf_list
  }

let lf_eta_extensionality
      (#a : Type) (#b : Type)
      (f : list_fun a b) (g : list_fun a b {g.lf_len = f.lf_len})
      (ef : squash (f == eta f)) (eg : squash (g == eta g))
      (eq : (x:a -> i : nat {i < f.lf_len} -> Lemma (index (f.lf_list x) i == index (g.lf_list x) i)))
  : Lemma (f == g)
  = U.funext_eta (eta f).lf_list (eta g).lf_list (_ by T.(trefl ())) (_ by T.(trefl ()))
                 (fun x -> list_extensionality (f.lf_list x) (g.lf_list x) (fun i -> eq x i))


/// Conversions with [list (a -> b)]

[@@ __list_fun__]
let lf_of_list_f (#a #b : Type) (l : list (a -> b))
                       (x : a)
  : l' : list b {length l' = length l}
  = map (U.app_on x b) l

unfold
let lf_of_list (#a #b : Type) (l : list (a -> b))
  : list_fun a b
  = {
    lf_len  = length l;
    lf_list = lf_of_list_f l
  }

[@@ __list_fun__]
let lf_index (#a #b : Type) (l : list_fun a b)
             (i : nat {i < l.lf_len}) (x : a)
  : b
  = index (l.lf_list x) i

unfold
let lf_to_list (#a #b : Type) (l : list_fun a b)
  : list (a -> b)
  = initi 0 l.lf_len (lf_index l)


/// Operations

unfold
let const (a #b : Type) (l : list b)
  : list_fun a b
  = {
    lf_len  = length l;
    lf_list = U.const a #(l' : list b {length l' = length l}) l
  }


[@@ __list_fun__]
let append_f #a #b (l0 l1 : list_fun a b) (x : a)
  : l : list b {length l = l0.lf_len + l1.lf_len}
  = (**) append_length (l0.lf_list x) (l1.lf_list x);
    append (l0.lf_list x) (l1.lf_list x)

unfold
let append (#a #b : Type) (l0 l1 : list_fun a b)
  : list_fun a b
  = {
    lf_len  = l0.lf_len + l1.lf_len;
    lf_list = append_f l0 l1
  }


[@@ __list_fun__]
let map_f #a #b #c (f : b -> c) (l : list_fun a b) (x : a)
  : l' : list c {length l' = l.lf_len}
  = map f (l.lf_list x)

unfold
let map #a #b #c (f : b -> c) (l : list_fun a b)
  : list_fun a c
  = {
    lf_len  = l.lf_len;
    lf_list = map_f f l
  }
