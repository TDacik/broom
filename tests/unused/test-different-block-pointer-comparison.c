#include <stdlib.h>

struct sll_node {
	int data;
	struct sll_node *next;
};

int p() {
	struct sll_node *p = malloc(sizeof(struct sll_node));
	struct sll_node *q = malloc(sizeof(struct sll_node));
	if (p<q) return 1;
	return 0;
}

