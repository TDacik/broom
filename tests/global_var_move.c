#include <stdlib.h>
struct sll_node {
	struct sll_node *next;
};

struct sll_node *x;

void pokus4() {
	struct sll_node *b;
	b=x->next; x=b;
	}
