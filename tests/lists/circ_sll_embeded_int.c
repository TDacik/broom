#include <stdlib.h>


struct sll {
    struct sll *next;
};

struct embeded_sll {
    int value;
    struct sll sll_head;
};

void init_sll(struct sll *x) {
	x->next=x;
}

void insert_after(struct sll *l, struct sll *item) {
	struct sll *next=l->next;
	item->next=next;
	l->next=item;
}



int main() {
	struct embeded_sll *x=malloc(sizeof (struct embeded_sll));
	init_sll(&(x->sll_head));
	struct embeded_sll *item=malloc(sizeof (struct embeded_sll));
	init_sll(&(item->sll_head));
	insert_after(&(x->sll_head),&(item->sll_head));
	//remove_item(&(item->sll_head)); // memory leak
	free(item);
	free(x);
	return 0;
}

