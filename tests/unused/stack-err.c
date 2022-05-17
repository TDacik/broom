#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

struct node {
	int i;
	int *j;
};

/* warning: function returns address of local variable */

int *return_stack_opt() {
	int a = 3;
	return &a; // no warning, optimized by gcc (!)
}

int *return_stack() {
	int a = 3;
	int *q = &a;
	return q; // warning
}

void argument_stack(struct node *s) {
	int a = 3;
	s->j = &a; // warning
}

void invalid_stack() {
	{
		struct node s = {3, NULL};
	}
}

/* error: attempt to free a non-heap object */

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

/* error: dereference of non-existing non-heap object */

int main() {
	struct node s;
	struct node *ptr_s = &s;
	argument_stack(ptr_s);
	int a;
	if (__VERIFIER_nondet_int())
		a = *(s.j); // error
	else
		a = *(return_stack()); // error
	return a;
}
