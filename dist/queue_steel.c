/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
 */

#include "queue_steel.h"



Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0
*Learn_Steel_QueueP_Test_p0_malloc()
{
  KRML_CHECK_SIZE(sizeof (Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0),
    (uint32_t)1U);
  Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0
  *q = KRML_HOST_MALLOC(sizeof (Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0));
  q[0U]
  =
    (
      (Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0){
        .q_exit = NULL,
        .q_entry = NULL
      }
    );
  return q;
}

void
Learn_Steel_QueueP_Test_p0_free(
  Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0 *q
)
{
  KRML_HOST_FREE(q);
}

bool
Learn_Steel_QueueP_Test_p0_is_empty(
  Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0 *q
)
{
  Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0 q_st = q[0U];
  return q_st.q_exit == NULL;
}

void
Learn_Steel_QueueP_Test_p0_enqueue(
  Learn_Steel_ListP_Test_cell0 *x,
  Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0 *q
)
{
  x->next = NULL;
  Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0 q_st = q[0U];
  if (q_st.q_entry == NULL)
    q[0U] =
      (
        (Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0){
          .q_exit = x,
          .q_entry = x
        }
      );
  else
  {
    Learn_Steel_ListP_Test_cell0 s = q_st.q_entry[0U];
    q_st.q_entry[0U] =
      ((Learn_Steel_ListP_Test_cell0){ .next = x, .data_x = s.data_x, .data_y = s.data_y });
    q->q_entry = x;
  }
}

Learn_Steel_ListP_Test_cell0
*Learn_Steel_QueueP_Test_p0_dequeue(
  Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0 *q
)
{
  Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0 q_st = q[0U];
  Learn_Steel_ListP_Test_cell0 *rt = q_st.q_exit;
  Learn_Steel_ListP_Test_cell0 s = rt[0U];
  Learn_Steel_ListP_Test_cell0 *nxt = s.next;
  q->q_exit = nxt;
  if (nxt == NULL)
    q->q_entry = NULL;
  return rt;
}

void Learn_Steel_QueueP_Test_test_p0()
{
  Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0
  *q = Learn_Steel_QueueP_Test_p0_malloc();
  KRML_CHECK_SIZE(sizeof (Learn_Steel_ListP_Test_cell0), (uint32_t)1U);
  Learn_Steel_ListP_Test_cell0 *x0 = KRML_HOST_MALLOC(sizeof (Learn_Steel_ListP_Test_cell0));
  x0[0U]
  = ((Learn_Steel_ListP_Test_cell0){ .next = NULL, .data_x = (uint32_t)0U, .data_y = true });
  Learn_Steel_QueueP_Test_p0_enqueue(x0, q);
  KRML_CHECK_SIZE(sizeof (Learn_Steel_ListP_Test_cell0), (uint32_t)1U);
  Learn_Steel_ListP_Test_cell0 *x1 = KRML_HOST_MALLOC(sizeof (Learn_Steel_ListP_Test_cell0));
  x1[0U]
  = ((Learn_Steel_ListP_Test_cell0){ .next = NULL, .data_x = (uint32_t)1U, .data_y = false });
  Learn_Steel_QueueP_Test_p0_enqueue(x1, q);
  Learn_Steel_ListP_Test_cell0 *x0_ = Learn_Steel_QueueP_Test_p0_dequeue(q);
  x0_->data_x = (uint32_t)2U;
  Learn_Steel_QueueP_Test_p0_enqueue(x0_, q);
  Learn_Steel_ListP_Test_cell0 *x1_ = Learn_Steel_QueueP_Test_p0_dequeue(q);
  Learn_Steel_ListP_Test_cell0 *x0_1 = Learn_Steel_QueueP_Test_p0_dequeue(q);
  KRML_HOST_FREE(x0_1);
  KRML_HOST_FREE(x1_);
  Learn_Steel_QueueP_Test_p0_free(q);
}

