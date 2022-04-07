module Learn.Steel.List.DataD

open Steel.Reference


#push-options "--__no_positivity"
noeq
type cell (a: Type0) = {
  next: ref (cell a);
  data: a;
}
#pop-options

