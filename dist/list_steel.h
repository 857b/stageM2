/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
 */

#ifndef __list_steel_H
#define __list_steel_H




#include <stdint.h>
#include "krml/internal/target.h"
typedef struct Learn_Steel_List_Data_cell__uint32_t_s Learn_Steel_List_Data_cell__uint32_t;

typedef struct Learn_Steel_List_Data_cell__uint32_t_s
{
  Learn_Steel_List_Data_cell__uint32_t *next;
  uint32_t data;
}
Learn_Steel_List_Data_cell__uint32_t;

uint32_t Learn_Steel_List_Impl_length__uint32_t(Learn_Steel_List_Data_cell__uint32_t *r);

extern uint32_t (*Learn_Steel_List_Impl_length_u32)(Learn_Steel_List_Data_cell__uint32_t *x0);

void
Learn_Steel_List_Impl_insert_aux__uint32_t(
  uint32_t i,
  Learn_Steel_List_Data_cell__uint32_t *x,
  Learn_Steel_List_Data_cell__uint32_t *entry
);

Learn_Steel_List_Data_cell__uint32_t
*Learn_Steel_List_Impl_insert__uint32_t(
  uint32_t i,
  Learn_Steel_List_Data_cell__uint32_t *x,
  Learn_Steel_List_Data_cell__uint32_t *entry
);

extern Learn_Steel_List_Data_cell__uint32_t
*(*Learn_Steel_List_Impl_insert_u32)(
  uint32_t x0,
  Learn_Steel_List_Data_cell__uint32_t *x1,
  Learn_Steel_List_Data_cell__uint32_t *x2
);

void
Learn_Steel_List_Impl_insert2_cell_gs_next__uint32_t(
  uint32_t i,
  Learn_Steel_List_Data_cell__uint32_t *x,
  Learn_Steel_List_Data_cell__uint32_t *r
);

void
Learn_Steel_List_Impl_insert2_u32(
  uint32_t i,
  Learn_Steel_List_Data_cell__uint32_t *x,
  Learn_Steel_List_Data_cell__uint32_t **r
);

Learn_Steel_List_Data_cell__uint32_t
*Learn_Steel_List_Impl_reverse_aux__uint32_t(
  Learn_Steel_List_Data_cell__uint32_t *r_f,
  Learn_Steel_List_Data_cell__uint32_t *r_r
);

Learn_Steel_List_Data_cell__uint32_t
*Learn_Steel_List_Impl_reverse__uint32_t(Learn_Steel_List_Data_cell__uint32_t *r);

extern Learn_Steel_List_Data_cell__uint32_t
*(*Learn_Steel_List_Impl_reverse_u32)(Learn_Steel_List_Data_cell__uint32_t *x0);


#define __list_steel_H_DEFINED
#endif
