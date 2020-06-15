#include <stdlib.h>

/* error: free called with offset << off << B */

struct sll_node {
	struct sll_node *next;
	struct sll_node *prev;
};

int main() {
	struct sll_node *p = malloc(sizeof(struct sll_node));
	void *q = &(p->prev);
	free(q); // invalid free
	return 0;
}
