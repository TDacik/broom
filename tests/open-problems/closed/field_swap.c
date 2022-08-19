/**
 * Why is the entailment_limit reached?
 * 
 */

#include <stdlib.h>

struct sll {
	int data;
	struct sll *next;
};

void loop(struct sll *x) {
	while (x != NULL) {
		x = x->next;
	}
}
