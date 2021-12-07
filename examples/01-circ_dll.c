#include <stdlib.h>


struct dll {
    struct dll *next;
    struct dll *prev;
};

struct emb_dll {
    int value;
    struct dll link;
};

// initialization of circular dll x
void init_dll(struct dll *x) {
	x->next=x;
	x->prev=x;
}

// add item j to list l
void insert_after(struct dll *l, struct dll *j) {
	struct dll *n = l->next;
	j->next = n;
	j->prev = l;
	l->next = j;
	n->prev = j;
}

int main() {
	struct emb_dll *x = malloc(sizeof (struct emb_dll));
	init_dll(&(x->link));
	struct emb_dll *i = malloc(sizeof (struct emb_dll));
	init_dll(&(i->link));
	insert_after(&(x->link), &(i->link));

	free(i);
	free(x);
	return 0;
}
