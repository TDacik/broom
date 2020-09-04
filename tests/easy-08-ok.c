#include <stdlib.h>
// #include <stdio.h>

struct sll_node {
	struct sll_node *next;
	struct sll_node *prev;
};

int main() {
	struct sll_node *p = malloc(sizeof(struct sll_node));
	p->prev = p;
	void *q = &(p->prev);
	struct sll_node *w = *((struct sll_node **)q); // problem with void*
	// printf("p=%x,q=%x,w=%x\n",p,q,w);
	free(w); // p == w
	return 0;
}
