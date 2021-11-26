#include <stdlib.h>


struct sll {
    struct sll *next;
};

struct embeded_sll2 {
    int value;
    struct sll sll_head1,sll_head2;
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



int test1() {
	struct embeded_sll2 *x=malloc(sizeof (struct embeded_sll2));
	init_sll(&(x->sll_head1));
	init_sll(&(x->sll_head2));
	struct embeded_sll *item=malloc(sizeof (struct embeded_sll));
	init_sll(&(item->sll_head));
	struct embeded_sll *item2=malloc(sizeof (struct embeded_sll));
	init_sll(&(item2->sll_head));
	insert_after(&(x->sll_head1),&(item->sll_head));
	insert_after(&(x->sll_head2),&(item2->sll_head));
	//remove_item(&(item->sll_head)); // memory leak
	free(item);
	free(item2);
	free(x);
	return 0;
}

int test2() {
	void *x=(void *) malloc(sizeof (struct embeded_sll2));
	init_sll((struct sll *) x+1);
	void *item=(void *) malloc(sizeof (struct embeded_sll2));
	init_sll((struct sll *) item+1);
	insert_after((struct sll *) x+1,(struct sll *) item+1);
	free(x);
	free(item);
}

