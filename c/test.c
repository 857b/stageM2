#include "stdio.h"

#include "list.h"
#include "queue.h"
#include "queue_steel.h"

typedef Learn_LowStar_List_Data_cell__uint32_t* list;

void print_list(list p) {
	if (p) {
		printf("%u", p->data);
		p = p->next;
	}
	while (p) {
		printf(" %u", p->data);
		p = p->next;
	}
	printf("\n");
}

void test_list() {
	printf ("=== test list ===\n");
	list l = Learn_LowStar_List_Impl_initi_id(2, 6);
	// 2 3 4 5
	print_list(l);
	// 5
	printf("%u\n", Learn_LowStar_List_Impl_index_u32(l, 3)); // 5
	// 5
	printf("%u\n", Learn_LowStar_List_Impl_index_loop_u32(l, 3)); // 5
	// 4
	printf("%u\n", Learn_LowStar_List_Impl_length_loop_u32(l));
	Learn_LowStar_List_Impl_insert_u32(1, 7, l);
	// 2 7 3 4 5
	print_list(l);
	Learn_LowStar_List_Impl_set_u32(2, 8, l);
	// 2 7 8 4 5
	print_list(l);
	Learn_LowStar_List_Impl_insert_loop_u32(3, 9, l);
	// 2 7 8 9 4 5
	print_list(l);
	l = Learn_LowStar_List_Impl_reverse_u32(l);
	// 5 4 9 8 7 2
	print_list(l);
	l = Learn_LowStar_List_Impl_reverse_u32(l);
	// 2 7 8 9 4 5
	print_list(l);
	Learn_LowStar_List_Impl_free_u32(l);
}

typedef Learn_LowStar_Queue_Test_cell qcell;
typedef Learn_LowStar_Queue_Prop_queue_st__Learn_LowStar_Queue_Test_cell* queue;

void test_queue() {
	printf("=== test queue ===\n");
	queue q = Learn_LowStar_Queue_Test_malloc();
	qcell cs[2];
	cs[0].data_x = 0;
	cs[1].data_x = 1;
	Learn_LowStar_Queue_Test_enqueue(cs+0, q);
	Learn_LowStar_Queue_Test_enqueue(cs+1, q);
	qcell *x0 =  Learn_LowStar_Queue_Test_dequeue(q);
	qcell *x1 =  Learn_LowStar_Queue_Test_dequeue(q);
	// 0 1
	printf("%u %u\n", x0->data_x, x1->data_x);
	Learn_LowStar_Queue_Test_free(q);
}

int main() {
	//test_list();
	//Learn_LowStar_Queue_Test_test_queue_spec();
	//test_queue();
	Learn_Steel_QueueP_Test_test_p0();
	return 0;
}
