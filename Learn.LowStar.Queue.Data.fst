module Learn.LowStar.Queue.Data

module B = LowStar.Buffer

#push-options "--__no_positivity"
noeq
type cell_ptr (a: Type0) =
  B.pointer_or_null (cell a)
and cell (a: Type0) = {
  next: cell_ptr a;
  data: a;
}
#pop-options

noeq
type queue_st (a : Type) = {
  q_exit  : cell_ptr a;
  q_entry : cell_ptr a;
}

type queue (a : Type) = B.pointer (queue_st a)
