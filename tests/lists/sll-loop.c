#include <stdlib.h>
int __VERIFIER_nondet_int(void);

struct sll_node {
	struct sll_node *next;
};

void sll_insert(struct sll_node **plist) {
    struct sll_node *p = malloc(sizeof(struct sll_node));
//     if (!p)
//         abort();
    p->next = (*plist);
    (*plist) = p;
}

void create_list(struct sll_node **list) {
	while (__VERIFIER_nondet_int()) {
		sll_insert(list);
	}
}
