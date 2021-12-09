#include <string.h>
#include <stdlib.h>

struct sll_node {
	int data;
	struct sll_node *next;
	int x;
	int y;
};

int main() {
	struct sll_node *p = alloca(sizeof(struct sll_node));
	p->data = 3;
	p->next = p;
	p->x = 4;
	p->y = 5;
	struct sll_node *q = alloca(sizeof(struct sll_node));
	int c = sizeof(*p);
	memcpy(q, p, c);
	return q->data + q->x + q->y;
}
