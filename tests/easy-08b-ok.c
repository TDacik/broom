#include <stdlib.h>

struct sll_node {
	struct sll_node *next;
	struct sll_node *prev;
};

int main() {
	struct sll_node *p = malloc(sizeof(struct sll_node));
	p->prev = p;
	struct sll_node ** q = &(p->prev);
	struct sll_node *w = *q;
	free(w); // p == w
	return 0;
}
