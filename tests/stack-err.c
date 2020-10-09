#include <stdlib.h>

struct node {
	int i;
	int *j;
};

int *return_stack_opt() {
	int a = 3;
	return &a; // no error, optimized by gcc (!)
}

int *return_stack() {
	int a = 3;
	int *q = &a;
	return q; // error
}

void argument_stack(struct node *s) {
	int a = 3;
	s->j = &a; // error
}

void invalid_stack() {
	{
		struct node s = {3, NULL};
	}
}

void free_stack() {
	struct node s = {3, NULL};
	void *q = &s;
	free(q); // error
}

void free_stack_off() {
	struct node s = {3, NULL};
	void *q = &(s.j);
	free(q); // error
}
