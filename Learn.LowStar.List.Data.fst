module Learn.LowStar.List.Data

module B = LowStar.Buffer

#push-options "--__no_positivity"
noeq
type t (a: Type0) =
  B.pointer_or_null (cell a)
and cell (a: Type0) = {
  next: t a;
  data: a;
}
#pop-options
