/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
 */

#include "experiment.h"



void Experiment_Steel_Test_Extract_test3(uint32_t *r0, uint32_t *r1)
{
  uint32_t x = r0[0U];
  r1[0U] = x + (uint32_t)1U;
}

void Experiment_Steel_Test_Extract_test3_LV(uint32_t *r0, uint32_t *r1)
{
  uint32_t x = r0[0U];
  r1[0U] = x + (uint32_t)1U;
}

void Experiment_Steel_Test_Extract_test3_LV_(uint32_t *r0, uint32_t *r1)
{
  uint32_t x = r0[0U];
  r1[0U] = x + (uint32_t)1U;
}

uint32_t Experiment_Steel_Test_Extract_test_ghost(uint32_t *r)
{
  return r[0U];
}

void Experiment_Steel_Test_Extract_test_slrewrite(uint32_t *r0, uint32_t *r1, uint32_t *r2)
{

}

void Experiment_Steel_Test_Extract_test_with_invariant_g(uint32_t *r1)
{

}

void Experiment_Steel_Test_Extract_test_for_loop_0(uint32_t *r0)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)10U; i++)
  {

  }
}

