/**
 * Why is analysis for loop diverging?
 * 
 */

#include <stdlib.h>

struct sll {
	struct sll *next;
	int *data;
};

void loop(struct sll *x) {
	while (x != NULL) {
		x->data = malloc(sizeof(int));
		x = x->next;
	}
}