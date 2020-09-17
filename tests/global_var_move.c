#include <stdlib.h>

/* warning: memory leak detected while assigning a static variable */

struct sll_node {
	struct sll_node *next;
};

struct sll_node *x;

void pokus4() {
	struct sll_node *b;
	b=x->next; x=b;
}

int main() {
	x = malloc(sizeof(struct sll_node));
	x->next = NULL;
	pokus4(); // memory leak
	free(x);
	return 0;
}
