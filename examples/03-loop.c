#include <stdlib.h>

struct sll {
	struct sll *next;
};

// traverse of list x
struct sll *loop(struct sll *x) {
	while (x != NULL) {
		x = x->next;
	}
}
