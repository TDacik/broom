#include <stdlib.h>

struct node {
	int i;
	int *j;
};

struct node g = {3, NULL};

int *return_glob() {
	return &g; // ok
}

void free_glob() {
	void *q = &g;
	free(q); // error
}

void free_glob_off() {
	void *q = &(g.j);
	free(q); // error
}
