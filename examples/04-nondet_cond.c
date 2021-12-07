#include <stdlib.h>
// #define TEST

struct item {
	struct item *next;
	struct item *prev;
};

struct item *f(struct item *x) {
	if (random())
		return x->next;
	else
		return x;
}

#ifdef TEST
int main()
{
    struct item *dll = NULL;
    struct item *next = f(dll);
    return 0;
}
#endif
