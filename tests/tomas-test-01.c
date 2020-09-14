#include <stdlib.h>

struct sll_node {
	struct sll_node *next;
};

int main() {
	struct sll_node *p;
	struct sll_node **q; 
	q=&(p->next);
	return 0;
}
