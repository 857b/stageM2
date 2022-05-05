/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: /home/ben/.switch/fstar/krml/krml -tmpdir dist/ -skip-compilation obj/prims.krml obj/FStar_Pervasives_Native.krml obj/FStar_Pervasives.krml obj/FStar_Range.krml obj/FStar_Tactics_Common.krml obj/FStar_VConfig.krml obj/FStar_Reflection_Types.krml obj/FStar_Tactics_Types.krml obj/FStar_Tactics_Result.krml obj/FStar_Tactics_Effect.krml obj/FStar_Squash.krml obj/FStar_Classical.krml obj/FStar_Reflection_Data.krml obj/FStar_Tactics_Builtins.krml obj/FStar_Reflection_Const.krml obj/FStar_List_Tot_Base.krml obj/FStar_Order.krml obj/FStar_Reflection_Builtins.krml obj/FStar_Reflection_Derived.krml obj/FStar_Reflection_Derived_Lemmas.krml obj/FStar_Reflection.krml obj/FStar_Tactics_Print.krml obj/FStar_Tactics_SyntaxHelpers.krml obj/FStar_StrongExcludedMiddle.krml obj/FStar_Classical_Sugar.krml obj/FStar_List_Tot_Properties.krml obj/FStar_List_Tot.krml obj/FStar_Tactics_Util.krml obj/FStar_Ghost.krml obj/FStar_IndefiniteDescription.krml obj/FStar_Reflection_Formula.krml obj/FStar_PropositionalExtensionality.krml obj/FStar_Tactics_Derived.krml obj/FStar_Tactics_Logic.krml obj/FStar_Tactics.krml obj/FStar_Preorder.krml obj/FStar_Calc.krml obj/FStar_Monotonic_Pure.krml obj/FStar_Universe.krml obj/FStar_MSTTotal.krml obj/FStar_NMSTTotal.krml obj/FStar_PCM.krml obj/FStar_FunctionalExtensionality.krml obj/FStar_Set.krml obj/FStar_PredicateExtensionality.krml obj/FStar_WellFounded.krml obj/FStar_Real.krml obj/FStar_MST.krml obj/FStar_Exn.krml obj/FStar_Monotonic_Witnessed.krml obj/FStar_ErasedLogic.krml obj/FStar_TSet.krml obj/FStar_Monotonic_Heap.krml obj/FStar_Heap.krml obj/FStar_ST.krml obj/FStar_All.krml obj/FStar_List.krml obj/FStar_Mul.krml obj/FStar_Seq_Base.krml obj/FStar_Seq_Properties.krml obj/FStar_Seq.krml obj/FStar_Math_Lib.krml obj/FStar_Math_Lemmas.krml obj/FStar_BitVector.krml obj/FStar_UInt.krml obj/FStar_UInt32.krml obj/FStar_Char.krml obj/FStar_String.krml obj/FStar_Tactics_CanonCommSwaps.krml obj/FStar_Algebra_CommMonoid_Equiv.krml obj/FStar_Tactics_CanonCommMonoidSimple_Equiv.krml obj/Learn_Util.krml obj/Learn_Tactics_Unsquash.krml obj/FStar_List_Pure_Base.krml obj/FStar_List_Pure_Properties.krml obj/FStar_List_Pure.krml obj/Learn_List.krml obj/Learn_ListFun.krml obj/FStar_Algebra_Monoid.krml obj/FStar_Fin.krml obj/Learn_Permutation.krml obj/Learn_Steel_Util.krml obj/Learn_Steel_ListP_Param.krml obj/Learn_Steel_ListP_Data.krml obj/Learn_Steel_ListP_Derived.krml obj/Learn_Steel_QueueP_Data.krml obj/FStar_Map.krml obj/FStar_Monotonic_HyperHeap.krml obj/Learn_DList.krml obj/FStar_GSet.krml obj/FStar_BigOps.krml obj/Learn_Steel_List_Data.krml obj/Learn_Steel_List_Derived.krml obj/Spec_Loops.krml obj/FStar_UInt64.krml obj/FStar_Monotonic_HyperStack.krml obj/FStar_HyperStack.krml obj/FStar_HyperStack_ST.krml obj/FStar_ModifiesGen.krml obj/LowStar_Monotonic_Buffer.krml obj/LowStar_Buffer.krml obj/LowStar_BufferOps.krml obj/C_Loops.krml obj/LowStar_Modifies.krml obj/Learn_LowStar.krml obj/Learn_LowStar_List_Data.krml obj/Learn_LowStar_Util.krml obj/Learn_LowStar_List_Prop.krml obj/Learn_LowStar_Loops.krml obj/Learn_LowStar_List_Impl.krml obj/Learn_LowStar_List.krml obj/Learn_Steel.krml obj/Learn_Steel_ListP_Impl.krml obj/Learn_Steel_QueueP_Impl.krml obj/Learn_Steel_QueueP.krml obj/Learn_Option.krml obj/Learn_LowStar_Queue_Param.krml obj/Learn_LowStar_Queue_Prop.krml obj/Learn_LowStar_Queue_Impl.krml obj/Learn_Logic.krml obj/Learn_Tactics_Test.krml obj/Learn_Steel_ListP.krml obj/Learn_Steel_ListP_Test.krml obj/Learn_LowStar_Queue.krml obj/Learn_LowStar_Queue_Test.krml obj/Learn_Steel_QueueP_Test.krml obj/Learn_Steel_List_Impl.krml -warn-error @4@5@18 -fparentheses -bundle LowStar.*,Prims,Learn.LowStar.Loops,C.Loops,FStar.*,Steel.*,Learn.Steel.Util,Learn.Tactics.*,Learn.Util,Learn.Permutation,Learn.DList,Learn.ListFun,Learn.Logic,Experiment.* -bundle Learn.LowStar.List+Learn.LowStar.List.Impl=Learn.LowStar.List.*[rename=list] -bundle Learn.LowStar.Queue.Test=Learn.LowStar.Queue,Learn.LowStar.Queue.*[rename=queue] -bundle Learn.Steel.List.Impl=Learn.Steel.List.*[rename=list_steel] -bundle Learn.Steel.ListP.Test=Learn.Steel.ListP.*[rename=list_param] -bundle Learn.Steel.QueueP.Test=Learn.Steel.QueueP.*[rename=queue_steel] -minimal -add-include <stdint.h> -add-include "krml/internal/target.h"
  F* version: 6e4b2188
  KaRaMeL version: fc64e65f
 */

#include "Learn_LowStar.h"



void
Learn_LowStar_buffer_copy_rec_aux__uint32_t(
  uint32_t *src,
  uint32_t *dst,
  uint32_t l,
  uint32_t i
)
{
  if (i < l)
  {
    dst[i] = src[i];
    Learn_LowStar_buffer_copy_rec_aux__uint32_t(src, dst, l, i + (uint32_t)1U);
  }
}

void Learn_LowStar_buffer_copy_rec__uint32_t(uint32_t *src, uint32_t *dst, uint32_t l)
{
  Learn_LowStar_buffer_copy_rec_aux__uint32_t(src, dst, l, (uint32_t)0U);
}

void
(*Learn_LowStar_buffer_copy_uint32)(uint32_t *x0, uint32_t *x1, uint32_t x2) =
  Learn_LowStar_buffer_copy_rec__uint32_t;

void Learn_LowStar_test_set_field(Learn_LowStar_test_struct *x)
{
  x->fld_a = (uint32_t)1U;
}

typedef uint32_t __uint32_t___;

uint32_t Learn_LowStar_test_rt_ghost_callee()
{
  return (uint32_t)0U;
}

uint32_t Learn_LowStar_test_rt_ghost_caller()
{
  uint32_t scrut = Learn_LowStar_test_rt_ghost_callee();
  return scrut;
}

void Learn_LowStar_test_ghost_pair()
{
  uint32_t x = (uint32_t)0U;
  x++;
}

uint32_t Learn_LowStar_test_struct_arg_callee(Learn_LowStar_test_struct p)
{
  return p.fld_a + p.fld_b;
}

uint32_t Learn_LowStar_test_struct_arg_caller()
{
  return (uint32_t)0U + (uint32_t)1U;
}

uint32_t Learn_LowStar_test_struct_arg()
{
  return (uint32_t)0U;
}

void Learn_LowStar_test_stateful_loop_guard(bool b)
{
  uint32_t x = (uint32_t)0U;
  x = (uint32_t)1U;
  bool cond = b;
  while (cond)
  {
    x = (uint32_t)1U;
    cond = b;
  }
}

uint32_t Learn_LowStar_tail_recursive(uint32_t acc, uint32_t i)
{
  if (i > (uint32_t)0U)
    return Learn_LowStar_tail_recursive(acc + i, i - (uint32_t)1U);
  else
    return acc;
}

uint32_t Learn_LowStar_inline_tail_call(uint32_t i)
{
  return Learn_LowStar_tail_recursive((uint32_t)0U, i) + (uint32_t)1U;
}

bool Learn_LowStar_ret_buf()
{
  bool b = true;
  return b;
}

bool Learn_LowStar_ret_buf_caller()
{
  bool b = true;
  return b;
}

void Learn_LowStar_f_call_u32__uint32_t(uint32_t x, bool b)
{
  if (b)
    Learn_LowStar_f_call_u32__uint32_t((uint32_t)0U, false);
}

void Learn_LowStar_f_call_u32__bool(bool x, bool b)
{
  if (b)
    Learn_LowStar_f_call_u32__uint32_t((uint32_t)0U, false);
}

void Learn_LowStar_f_call_u32_caller()
{
  Learn_LowStar_f_call_u32__bool(false, true);
}
