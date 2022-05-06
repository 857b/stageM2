/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: /home/ben/.switch/fstar/krml/krml -tmpdir dist/ -skip-compilation obj/prims.krml obj/FStar_Pervasives_Native.krml obj/FStar_Pervasives.krml obj/FStar_Range.krml obj/FStar_Tactics_Common.krml obj/FStar_VConfig.krml obj/FStar_Reflection_Types.krml obj/FStar_Tactics_Types.krml obj/FStar_Tactics_Result.krml obj/FStar_Tactics_Effect.krml obj/FStar_Squash.krml obj/FStar_Classical.krml obj/FStar_Reflection_Data.krml obj/FStar_Tactics_Builtins.krml obj/FStar_Reflection_Const.krml obj/FStar_List_Tot_Base.krml obj/FStar_Order.krml obj/FStar_Reflection_Builtins.krml obj/FStar_Reflection_Derived.krml obj/FStar_Reflection_Derived_Lemmas.krml obj/FStar_Reflection.krml obj/FStar_Tactics_Print.krml obj/FStar_Tactics_SyntaxHelpers.krml obj/FStar_StrongExcludedMiddle.krml obj/FStar_Classical_Sugar.krml obj/FStar_List_Tot_Properties.krml obj/FStar_List_Tot.krml obj/FStar_Tactics_Util.krml obj/FStar_Ghost.krml obj/FStar_IndefiniteDescription.krml obj/FStar_Reflection_Formula.krml obj/FStar_PropositionalExtensionality.krml obj/FStar_Tactics_Derived.krml obj/FStar_Tactics_Logic.krml obj/FStar_Tactics.krml obj/FStar_Preorder.krml obj/FStar_Calc.krml obj/FStar_Monotonic_Pure.krml obj/FStar_Universe.krml obj/FStar_MSTTotal.krml obj/FStar_NMSTTotal.krml obj/FStar_PCM.krml obj/FStar_FunctionalExtensionality.krml obj/FStar_Set.krml obj/FStar_PredicateExtensionality.krml obj/FStar_WellFounded.krml obj/FStar_Real.krml obj/FStar_MST.krml obj/FStar_Exn.krml obj/FStar_Monotonic_Witnessed.krml obj/FStar_ErasedLogic.krml obj/FStar_TSet.krml obj/FStar_Monotonic_Heap.krml obj/FStar_Heap.krml obj/FStar_ST.krml obj/FStar_All.krml obj/FStar_List.krml obj/FStar_Mul.krml obj/FStar_Seq_Base.krml obj/FStar_Seq_Properties.krml obj/FStar_Seq.krml obj/FStar_Math_Lib.krml obj/FStar_Math_Lemmas.krml obj/FStar_BitVector.krml obj/FStar_UInt.krml obj/FStar_UInt32.krml obj/FStar_Char.krml obj/FStar_String.krml obj/FStar_Tactics_CanonCommSwaps.krml obj/FStar_Algebra_CommMonoid_Equiv.krml obj/FStar_Tactics_CanonCommMonoidSimple_Equiv.krml obj/Learn_Util.krml obj/Learn_Tactics_Unsquash.krml obj/FStar_List_Pure_Base.krml obj/FStar_List_Pure_Properties.krml obj/FStar_List_Pure.krml obj/Learn_List.krml obj/Learn_ListFun.krml obj/FStar_Algebra_Monoid.krml obj/FStar_Fin.krml obj/Learn_Permutation.krml obj/Learn_Steel_Util.krml obj/Learn_Steel_ListP_Param.krml obj/Learn_Steel_ListP_Data.krml obj/Learn_Steel_ListP_Derived.krml obj/Learn_Steel_QueueP_Data.krml obj/FStar_Map.krml obj/FStar_Monotonic_HyperHeap.krml obj/Learn_Option.krml obj/Learn_Logic.krml obj/Learn_DList.krml obj/FStar_GSet.krml obj/FStar_BigOps.krml obj/Learn_Steel_List_Data.krml obj/Learn_Steel_List_Derived.krml obj/Spec_Loops.krml obj/FStar_UInt64.krml obj/FStar_Monotonic_HyperStack.krml obj/FStar_HyperStack.krml obj/FStar_HyperStack_ST.krml obj/FStar_ModifiesGen.krml obj/LowStar_Monotonic_Buffer.krml obj/LowStar_Buffer.krml obj/LowStar_BufferOps.krml obj/C_Loops.krml obj/LowStar_Modifies.krml obj/Learn_LowStar.krml obj/Learn_LowStar_List_Data.krml obj/Learn_LowStar_Util.krml obj/Learn_LowStar_List_Prop.krml obj/Learn_LowStar_Loops.krml obj/Learn_LowStar_List_Impl.krml obj/Learn_LowStar_List.krml obj/Learn_Steel.krml obj/Learn_Steel_ListP_Impl.krml obj/Learn_Steel_QueueP_Impl.krml obj/Learn_Steel_QueueP.krml obj/Learn_LowStar_Queue_Param.krml obj/Learn_LowStar_Queue_Prop.krml obj/Learn_LowStar_Queue_Impl.krml obj/Learn_Tactics_Test.krml obj/Learn_Steel_ListP.krml obj/Learn_Steel_ListP_Test.krml obj/Learn_LowStar_Queue.krml obj/Learn_LowStar_Queue_Test.krml obj/Learn_Steel_QueueP_Test.krml obj/Learn_Steel_List_Impl.krml -warn-error @4@5@18 -fparentheses -bundle LowStar.*,Prims,Learn.LowStar.Loops,C.Loops,FStar.*,Steel.*,Learn.Steel.Util,Learn.Tactics.*,Learn.Util,Learn.Permutation,Learn.DList,Learn.ListFun,Learn.Logic,Experiment.* -bundle Learn.LowStar.List+Learn.LowStar.List.Impl=Learn.LowStar.List.*[rename=list] -bundle Learn.LowStar.Queue.Test=Learn.LowStar.Queue,Learn.LowStar.Queue.*[rename=queue] -bundle Learn.Steel.List.Impl=Learn.Steel.List.*[rename=list_steel] -bundle Learn.Steel.ListP.Test=Learn.Steel.ListP.*[rename=list_param] -bundle Learn.Steel.QueueP.Test=Learn.Steel.QueueP.*[rename=queue_steel] -minimal -add-include <stdint.h> -add-include "krml/internal/target.h"
  F* version: 6e4b2188
  KaRaMeL version: fc64e65f
 */

#ifndef __list_H
#define __list_H




#include <stdint.h>
#include "krml/internal/target.h"
typedef struct Learn_LowStar_List_Data_cell__uint32_t_s Learn_LowStar_List_Data_cell__uint32_t;

typedef struct Learn_LowStar_List_Data_cell__uint32_t_s
{
  Learn_LowStar_List_Data_cell__uint32_t *next;
  uint32_t data;
}
Learn_LowStar_List_Data_cell__uint32_t;

uint32_t
Learn_LowStar_List_Impl_length_loop__uint32_t(Learn_LowStar_List_Data_cell__uint32_t *p);

extern uint32_t
(*Learn_LowStar_List_Impl_length_loop_u32)(Learn_LowStar_List_Data_cell__uint32_t *x0);

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_initi__uint32_t(uint32_t lb, uint32_t ub, uint32_t (*f)(uint32_t x0));

extern Learn_LowStar_List_Data_cell__uint32_t
*(*Learn_LowStar_List_Impl_initi_u32)(uint32_t x0, uint32_t x1, uint32_t (*x2)(uint32_t x0));

uint32_t Learn_LowStar_List_Impl_initi_id_f(uint32_t i);

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_initi_id(uint32_t lb, uint32_t ub);

uint32_t
Learn_LowStar_List_Impl_index__uint32_t(Learn_LowStar_List_Data_cell__uint32_t *p, uint32_t i);

extern uint32_t
(*Learn_LowStar_List_Impl_index_u32)(Learn_LowStar_List_Data_cell__uint32_t *x0, uint32_t x1);

uint32_t
Learn_LowStar_List_Impl_index_loop__uint32_t(
  Learn_LowStar_List_Data_cell__uint32_t *p,
  uint32_t i
);

extern uint32_t
(*Learn_LowStar_List_Impl_index_loop_u32)(
  Learn_LowStar_List_Data_cell__uint32_t *x0,
  uint32_t x1
);

void
Learn_LowStar_List_Impl_insert_aux__uint32_t(
  uint32_t i,
  uint32_t x,
  Learn_LowStar_List_Data_cell__uint32_t *p
);

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_insert__uint32_t(
  uint32_t i,
  uint32_t x,
  Learn_LowStar_List_Data_cell__uint32_t *p
);

extern Learn_LowStar_List_Data_cell__uint32_t
*(*Learn_LowStar_List_Impl_insert_u32)(
  uint32_t x0,
  uint32_t x1,
  Learn_LowStar_List_Data_cell__uint32_t *x2
);

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_insert_loop__uint32_t(
  uint32_t i,
  uint32_t x,
  Learn_LowStar_List_Data_cell__uint32_t *p
);

extern Learn_LowStar_List_Data_cell__uint32_t
*(*Learn_LowStar_List_Impl_insert_loop_u32)(
  uint32_t x0,
  uint32_t x1,
  Learn_LowStar_List_Data_cell__uint32_t *x2
);

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_forward_u32(uint32_t i, Learn_LowStar_List_Data_cell__uint32_t *p);

void
Learn_LowStar_List_Impl_set__uint32_t(
  uint32_t i,
  uint32_t x,
  Learn_LowStar_List_Data_cell__uint32_t *p
);

extern void
(*Learn_LowStar_List_Impl_set_u32)(
  uint32_t x0,
  uint32_t x1,
  Learn_LowStar_List_Data_cell__uint32_t *x2
);

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_last__uint32_t(Learn_LowStar_List_Data_cell__uint32_t *p);

extern Learn_LowStar_List_Data_cell__uint32_t
*(*Learn_LowStar_List_Impl_last_u32)(Learn_LowStar_List_Data_cell__uint32_t *x0);

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_append__uint32_t(
  Learn_LowStar_List_Data_cell__uint32_t *p0,
  Learn_LowStar_List_Data_cell__uint32_t *p1
);

extern Learn_LowStar_List_Data_cell__uint32_t
*(*Learn_LowStar_List_Impl_append_u32)(
  Learn_LowStar_List_Data_cell__uint32_t *x0,
  Learn_LowStar_List_Data_cell__uint32_t *x1
);

Learn_LowStar_List_Data_cell__uint32_t
*Learn_LowStar_List_Impl_reverse__uint32_t(Learn_LowStar_List_Data_cell__uint32_t *p);

extern Learn_LowStar_List_Data_cell__uint32_t
*(*Learn_LowStar_List_Impl_reverse_u32)(Learn_LowStar_List_Data_cell__uint32_t *x0);

void Learn_LowStar_List_Impl_free__uint32_t(Learn_LowStar_List_Data_cell__uint32_t *p);

extern void (*Learn_LowStar_List_Impl_free_u32)(Learn_LowStar_List_Data_cell__uint32_t *x0);

void Learn_LowStar_List_Impl_test_for();

void Learn_LowStar_List_Impl_test_ghost();

void Learn_LowStar_List_Impl_test();


#define __list_H_DEFINED
#endif
