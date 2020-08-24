#include <stdlib.h>

/* warning: memory leak detected while assigning a variable on stack */

struct sll_node {
	struct sll_node *next;
	int size;
};

int main() {
	struct sll_node *p = malloc(sizeof(struct sll_node));
	p = malloc(p->size);

	return 0;
}
