/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
 */

#ifndef __queue_steel_H
#define __queue_steel_H



#include "list_param.h"
#include <stdint.h>
#include "krml/internal/target.h"
typedef struct Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0_s
{
  Learn_Steel_ListP_Test_cell0 *q_exit;
  Learn_Steel_ListP_Test_cell0 *q_entry;
}
Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0;

typedef Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0
*Learn_Steel_QueueP_Test_p0_queue_t;

Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0
*Learn_Steel_QueueP_Test_p0_malloc();

void
Learn_Steel_QueueP_Test_p0_free(
  Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0 *q
);

bool
Learn_Steel_QueueP_Test_p0_is_empty(
  Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0 *q
);

void
Learn_Steel_QueueP_Test_p0_enqueue(
  Learn_Steel_ListP_Test_cell0 *x,
  Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0 *q
);

Learn_Steel_ListP_Test_cell0
*Learn_Steel_QueueP_Test_p0_dequeue(
  Learn_Steel_QueueP_Data_queue_st__Learn_Steel_ListP_Test_cell0 *q
);

void Learn_Steel_QueueP_Test_test_p0();


#define __queue_steel_H_DEFINED
#endif
