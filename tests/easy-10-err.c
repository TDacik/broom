#include <stdlib.h>

/* warning: memory leak detected while assigning a variable on stack */

struct sll_node {
	struct sll_node *next;
};

int main() {
	struct sll_node *p = malloc(sizeof(struct sll_node));
	p->next = malloc(sizeof(struct sll_node));
	p = p->next; // memory leak rewrite
	free(p);
	return 0;
}