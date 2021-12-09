#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

struct item {
	struct item *next;
	struct item *prev;
};

struct item *f(struct item *x) {
	if (random())
		return x;
	else {
		struct item * y = x->next;
		return y;
    }
}

int main()
{
    struct item *dll = NULL;

    struct item *next = f(dll);

    return 0;
}
