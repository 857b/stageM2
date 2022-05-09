/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
 */

#ifndef __Learn_LowStar_H
#define __Learn_LowStar_H




#include <stdint.h>
#include "krml/internal/target.h"
void
Learn_LowStar_buffer_copy_rec_aux__uint32_t(
  uint32_t *src,
  uint32_t *dst,
  uint32_t l,
  uint32_t i
);

void Learn_LowStar_buffer_copy_rec__uint32_t(uint32_t *src, uint32_t *dst, uint32_t l);

extern void (*Learn_LowStar_buffer_copy_uint32)(uint32_t *x0, uint32_t *x1, uint32_t x2);

typedef struct Learn_LowStar_test_struct_s
{
  uint32_t fld_a;
  uint32_t fld_b;
}
Learn_LowStar_test_struct;

void Learn_LowStar_test_set_field(Learn_LowStar_test_struct *x);

uint32_t Learn_LowStar_test_rt_ghost_callee();

uint32_t Learn_LowStar_test_rt_ghost_caller();

void Learn_LowStar_test_ghost_pair();

uint32_t Learn_LowStar_test_struct_arg_callee(Learn_LowStar_test_struct p);

uint32_t Learn_LowStar_test_struct_arg_caller();

uint32_t Learn_LowStar_test_struct_arg();

void Learn_LowStar_test_stateful_loop_guard(bool b);

uint32_t Learn_LowStar_tail_recursive(uint32_t acc, uint32_t i);

uint32_t Learn_LowStar_inline_tail_call(uint32_t i);

bool Learn_LowStar_ret_buf();

bool Learn_LowStar_ret_buf_caller();

void Learn_LowStar_f_call_u32__uint32_t(uint32_t x, bool b);

void Learn_LowStar_f_call_u32__bool(bool x, bool b);

void Learn_LowStar_f_call_u32_caller();


#define __Learn_LowStar_H_DEFINED
#endif
