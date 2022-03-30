#include "stdio.h"

#include "list.h"

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

int main() {
	printf ("=== test ===\n");
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
	return 0;
}
