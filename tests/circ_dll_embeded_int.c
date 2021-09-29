#include <stdlib.h>


struct dll {
    struct dll *next;
    struct dll *prev;
};

struct embeded_dll {
    int value;
    struct dll dll_head;
};

void init_dll(struct dll *x) {
	x->next=x;
	x->prev=x;
}

void insert_after(struct dll *l, struct dll *item) {
	struct dll *next=l->next;
	item->next=next;
	item->prev=l;
	l->next=item;
	next->prev=item;
}

void remove_item(struct dll *item) {
	struct dll *n=item->next;
	struct dll *p=item->prev;
	n->prev=p;
	p->next=n;
}

int main() {
	struct embeded_dll *x=malloc(sizeof (struct embeded_dll));
	init_dll(&(x->dll_head));
	struct embeded_dll *item=malloc(sizeof (struct embeded_dll));
	init_dll(&(item->dll_head));
	insert_after(&(x->dll_head),&(item->dll_head));
	remove_item(&(item->dll_head)); // memory leak
	free(item);
	free(x);
	return 0;
}

