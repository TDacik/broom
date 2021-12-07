#include <stdlib.h>

struct sll {
	struct sll *next;
};

// add item at the end of the list x
struct sll *a(struct sll *x) {
	if (x == NULL) {
		struct sll *y = malloc(sizeof (struct sll));
		y->next = NULL;
		x = y;
	}
    return x;
}
