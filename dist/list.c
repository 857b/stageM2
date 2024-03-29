/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
 */

#include "list.h"



uint32_t
Learn_LowStar_List_Impl_length_loop__uint32_t(Learn_LowStar_List_Data_cell__uint32_t *p)
{
  Learn_LowStar_List_Data_cell__uint32_t *p1 = p;
  uint32_t count = (uint32_t)0U;
  while (!(p1 == NULL))
  {
    p1 = p1->next;
    count++;
  }
  return count;
}

uint32_t
(*Learn_LowStar_List_Impl_length_loop_u32)(Learn_LowStar_List_Data_cell__uint32_t *x0) =
  Learn_LowStar_List_Impl_length_loop__uint32_t;

typedef Learn_LowStar_List_Data_cell__uint32_t
*dtuple2___Learn_LowStar_List_Data_cell__uint32_t____;

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_initi__uint32_t(uint32_t lb, uint32_t ub, uint32_t (*f)(uint32_t x0))
{
  if (lb < ub)
  {
    Learn_LowStar_List_Data_cell__uint32_t
    *scrut = Learn_LowStar_List_Impl_initi__uint32_t(lb + (uint32_t)1U, ub, f);
    Learn_LowStar_List_Data_cell__uint32_t *p_ = scrut;
    KRML_CHECK_SIZE(sizeof (Learn_LowStar_List_Data_cell__uint32_t), (uint32_t)1U);
    Learn_LowStar_List_Data_cell__uint32_t
    *p = KRML_HOST_MALLOC(sizeof (Learn_LowStar_List_Data_cell__uint32_t));
    p[0U] = ((Learn_LowStar_List_Data_cell__uint32_t){ .next = p_, .data = f(lb) });
    return p;
  }
  else
    return NULL;
}

Learn_LowStar_List_Data_cell__uint32_t
*(*Learn_LowStar_List_Impl_initi_u32)(uint32_t x0, uint32_t x1, uint32_t (*x2)(uint32_t x0)) =
  Learn_LowStar_List_Impl_initi__uint32_t;

uint32_t Learn_LowStar_List_Impl_initi_id_f(uint32_t i)
{
  return i;
}

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_initi_id(uint32_t lb, uint32_t ub)
{
  return Learn_LowStar_List_Impl_initi__uint32_t(lb, ub, Learn_LowStar_List_Impl_initi_id_f);
}

uint32_t
Learn_LowStar_List_Impl_index__uint32_t(Learn_LowStar_List_Data_cell__uint32_t *p, uint32_t i)
{
  if (i == (uint32_t)0U)
    return p->data;
  else
    return Learn_LowStar_List_Impl_index__uint32_t(p->next, i - (uint32_t)1U);
}

uint32_t
(*Learn_LowStar_List_Impl_index_u32)(Learn_LowStar_List_Data_cell__uint32_t *x0, uint32_t x1) =
  Learn_LowStar_List_Impl_index__uint32_t;

typedef struct ___________s {  } __________;

uint32_t
Learn_LowStar_List_Impl_index_loop__uint32_t(
  Learn_LowStar_List_Data_cell__uint32_t *p,
  uint32_t i
)
{
  Learn_LowStar_List_Data_cell__uint32_t *p_ = p;
  for (uint32_t i0 = (uint32_t)0U; i0 < i; i0++)
    p_ = p_->next;
  return p_->data;
}

uint32_t
(*Learn_LowStar_List_Impl_index_loop_u32)(
  Learn_LowStar_List_Data_cell__uint32_t *x0,
  uint32_t x1
) = Learn_LowStar_List_Impl_index_loop__uint32_t;

void
Learn_LowStar_List_Impl_insert_aux__uint32_t(
  uint32_t i,
  uint32_t x,
  Learn_LowStar_List_Data_cell__uint32_t *p
)
{
  if (i == (uint32_t)1U)
  {
    KRML_CHECK_SIZE(sizeof (Learn_LowStar_List_Data_cell__uint32_t), (uint32_t)1U);
    Learn_LowStar_List_Data_cell__uint32_t
    *p_f = KRML_HOST_MALLOC(sizeof (Learn_LowStar_List_Data_cell__uint32_t));
    p_f[0U] = ((Learn_LowStar_List_Data_cell__uint32_t){ .next = p->next, .data = x });
    p[0U] = ((Learn_LowStar_List_Data_cell__uint32_t){ .next = p_f, .data = p->data });
  }
  else
    Learn_LowStar_List_Impl_insert_aux__uint32_t(i - (uint32_t)1U, x, p->next);
}

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_insert__uint32_t(
  uint32_t i,
  uint32_t x,
  Learn_LowStar_List_Data_cell__uint32_t *p
)
{
  if (i == (uint32_t)0U)
  {
    KRML_CHECK_SIZE(sizeof (Learn_LowStar_List_Data_cell__uint32_t), (uint32_t)1U);
    Learn_LowStar_List_Data_cell__uint32_t
    *rt = KRML_HOST_MALLOC(sizeof (Learn_LowStar_List_Data_cell__uint32_t));
    rt[0U] = ((Learn_LowStar_List_Data_cell__uint32_t){ .next = p, .data = x });
    return rt;
  }
  else
  {
    Learn_LowStar_List_Impl_insert_aux__uint32_t(i, x, p);
    return p;
  }
}

Learn_LowStar_List_Data_cell__uint32_t
*(*Learn_LowStar_List_Impl_insert_u32)(
  uint32_t x0,
  uint32_t x1,
  Learn_LowStar_List_Data_cell__uint32_t *x2
) = Learn_LowStar_List_Impl_insert__uint32_t;

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_insert_loop__uint32_t(
  uint32_t i,
  uint32_t x,
  Learn_LowStar_List_Data_cell__uint32_t *p
)
{
  if (i == (uint32_t)0U)
  {
    KRML_CHECK_SIZE(sizeof (Learn_LowStar_List_Data_cell__uint32_t), (uint32_t)1U);
    Learn_LowStar_List_Data_cell__uint32_t
    *rt = KRML_HOST_MALLOC(sizeof (Learn_LowStar_List_Data_cell__uint32_t));
    rt[0U] = ((Learn_LowStar_List_Data_cell__uint32_t){ .next = p, .data = x });
    return rt;
  }
  else
  {
    Learn_LowStar_List_Data_cell__uint32_t *l_p = p;
    for (uint32_t i0 = (uint32_t)0U; i0 < i - (uint32_t)1U; i0++)
      l_p = l_p->next;
    KRML_CHECK_SIZE(sizeof (Learn_LowStar_List_Data_cell__uint32_t), (uint32_t)1U);
    Learn_LowStar_List_Data_cell__uint32_t
    *p_f = KRML_HOST_MALLOC(sizeof (Learn_LowStar_List_Data_cell__uint32_t));
    p_f[0U] = ((Learn_LowStar_List_Data_cell__uint32_t){ .next = l_p->next, .data = x });
    l_p[0U] = ((Learn_LowStar_List_Data_cell__uint32_t){ .next = p_f, .data = l_p->data });
    return p;
  }
}

Learn_LowStar_List_Data_cell__uint32_t
*(*Learn_LowStar_List_Impl_insert_loop_u32)(
  uint32_t x0,
  uint32_t x1,
  Learn_LowStar_List_Data_cell__uint32_t *x2
) = Learn_LowStar_List_Impl_insert_loop__uint32_t;

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_forward_u32(uint32_t i, Learn_LowStar_List_Data_cell__uint32_t *p)
{
  Learn_LowStar_List_Data_cell__uint32_t *l_p = p;
  for (uint32_t i0 = (uint32_t)0U; i0 < i; i0++)
    l_p = l_p->next;
  return l_p;
}

void
Learn_LowStar_List_Impl_set__uint32_t(
  uint32_t i,
  uint32_t x,
  Learn_LowStar_List_Data_cell__uint32_t *p
)
{
  Learn_LowStar_List_Data_cell__uint32_t *l_p = p;
  for (uint32_t i0 = (uint32_t)0U; i0 < i; i0++)
    l_p = l_p->next;
  Learn_LowStar_List_Data_cell__uint32_t *p_ = l_p;
  p_[0U] = ((Learn_LowStar_List_Data_cell__uint32_t){ .next = p_->next, .data = x });
}

void
(*Learn_LowStar_List_Impl_set_u32)(
  uint32_t x0,
  uint32_t x1,
  Learn_LowStar_List_Data_cell__uint32_t *x2
) = Learn_LowStar_List_Impl_set__uint32_t;

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_last__uint32_t(Learn_LowStar_List_Data_cell__uint32_t *p)
{
  Learn_LowStar_List_Data_cell__uint32_t *it = p;
  while (!(it->next == NULL))
    it = it->next;
  return it;
}

Learn_LowStar_List_Data_cell__uint32_t
*(*Learn_LowStar_List_Impl_last_u32)(Learn_LowStar_List_Data_cell__uint32_t *x0) =
  Learn_LowStar_List_Impl_last__uint32_t;

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_append__uint32_t(
  Learn_LowStar_List_Data_cell__uint32_t *p0,
  Learn_LowStar_List_Data_cell__uint32_t *p1
)
{
  if (p0 == NULL)
    return p1;
  else
  {
    Learn_LowStar_List_Data_cell__uint32_t *p0_last = Learn_LowStar_List_Impl_last__uint32_t(p0);
    p0_last[0U] = ((Learn_LowStar_List_Data_cell__uint32_t){ .next = p1, .data = p0_last->data });
    return p0;
  }
}

Learn_LowStar_List_Data_cell__uint32_t
*(*Learn_LowStar_List_Impl_append_u32)(
  Learn_LowStar_List_Data_cell__uint32_t *x0,
  Learn_LowStar_List_Data_cell__uint32_t *x1
) = Learn_LowStar_List_Impl_append__uint32_t;

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_reverse__uint32_t(Learn_LowStar_List_Data_cell__uint32_t *p)
{
  Learn_LowStar_List_Data_cell__uint32_t *it_f = p;
  Learn_LowStar_List_Data_cell__uint32_t *it_r = NULL;
  while (!(it_f == NULL))
  {
    Learn_LowStar_List_Data_cell__uint32_t *cell = it_f;
    it_f = cell->next;
    cell[0U] = ((Learn_LowStar_List_Data_cell__uint32_t){ .next = it_r, .data = cell->data });
    it_r = cell;
  }
  return it_r;
}

Learn_LowStar_List_Data_cell__uint32_t
*(*Learn_LowStar_List_Impl_reverse_u32)(Learn_LowStar_List_Data_cell__uint32_t *x0) =
  Learn_LowStar_List_Impl_reverse__uint32_t;

void Learn_LowStar_List_Impl_free__uint32_t(Learn_LowStar_List_Data_cell__uint32_t *p)
{
  if (!(p == NULL))
  {
    Learn_LowStar_List_Data_cell__uint32_t *p_next = p->next;
    KRML_HOST_FREE(p);
    Learn_LowStar_List_Impl_free__uint32_t(p_next);
  }
}

void
(*Learn_LowStar_List_Impl_free_u32)(Learn_LowStar_List_Data_cell__uint32_t *x0) =
  Learn_LowStar_List_Impl_free__uint32_t;

void Learn_LowStar_List_Impl_test_for()
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)10U; i++)
  {

  }
}

void Learn_LowStar_List_Impl_test_ghost()
{

}

void Learn_LowStar_List_Impl_test()
{
  Learn_LowStar_List_Data_cell__uint32_t b = { .next = NULL, .data = (uint32_t)42U };
}

