#include <stdlib.h>


struct sll_item {
    struct sll_item *next;
    int data;
};

struct sll_item * e(struct sll_item *y, struct sll_item *z, struct sll_item *v, 
  struct sll_item *w)
{
	if(random())
		return y->next;
	if(random())
		return z->next;
	if(random())
		return v->next;
	return w->next;
}

struct sll_item  *f(struct sll_item *y, struct sll_item *z)
{ 
	if(random()) {
		y = y->next; 
		y = y->next; 
		return z->next;
	}
	else {
		z = z->next;
		z = z->next;
		return y->next;
	}
}

struct sll_item  *g(struct sll_item *y, struct sll_item *z)
{ 
    if(random()) {
		y = y->next; 
	}
    else {
		z = z->next;
	}
    if(random()) {
		return y->next; 
	}
    else {
		return z->next;
	}
}
	