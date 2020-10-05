#include <stdlib.h>

/* error: use after free - dereference of already deleted heap object */

struct sll_node {
	struct sll_node *next;
};

void s(struct sll_node *x) {
	struct sll_node * y = x->next;
	free(x);
	y = x->next; // use after free
}
