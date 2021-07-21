#include <stdlib.h>


struct dll {
    struct dll *next;
    struct dll *prev;
};

struct dll *create_dll() {
	struct dll *x=malloc(sizeof(struct dll));
	x-> next=x;
	x->prev=x;
	return x;
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
	free(item);
}

int main() {
	struct dll *x=create_dll();
	struct dll *item=create_dll();
	insert_after(x,item);
	remove_item(item);
	return 0;
}

