#include <stdlib.h>

struct sll_node {
	struct sll_node *next;
};

int main() {
	struct sll_node *p = malloc(sizeof(struct sll_node));
	p->next = NULL;
	free(p);
	return 0;
}
