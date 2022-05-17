#include <stdlib.h>


struct sll_item {
    struct sll_item *next;
    int data;
};

struct sll_item * f(struct sll_item *y, struct sll_item *z)
{
	if(random())
		return y->next;
	else
		return z->next;
}

int g() {
    struct sll_item *p = malloc(sizeof(struct sll_item));
    struct sll_item *q = malloc(sizeof(struct sll_item));
    //p->next = q;
    f(p,q);
    free(p);
    free(q);
}
