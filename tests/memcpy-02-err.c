#include <string.h>
#include <stdlib.h>

struct sll_node {
	int data;
	struct sll_node *next;
};

struct sll_node * s() {
	struct sll_node *p = malloc(sizeof(struct sll_node));
	p->data = 3;
	p->next = p;
	struct sll_node *q = malloc(sizeof(struct sll_node));
	int c = sizeof(*p);
	memcpy(q, p, c);
	return q; // memory leak - p
}
