#include <string.h>
#include <stdlib.h>

struct sll_node {
	int data;
	struct sll_node *next;
};

int main() {
	struct sll_node *p = alloca(sizeof(struct sll_node));
	p->data = 3;
	p->next = p;
	struct sll_node *q = alloca(sizeof(struct sll_node));
	int c = sizeof(*p);
	memcpy(q, p, c);
	return q->data;
}
