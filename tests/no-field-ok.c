#include <stdlib.h>

struct item {
    struct item *next;
    struct item *prev;
};

extern void __VERIFIER_plot(const char *name, ...);

struct item* create_item(struct item *end)
{
    struct item *pi = malloc(sizeof(*pi));
    pi->next = end;
    return pi;
}

int main() {
	struct item *pi = calloc(1,sizeof(*pi));
	int *px = ((char*)pi)+2;
	*px = 9;
	struct item * elm = create_item(pi->next);
	__VERIFIER_plot("aa");
	free(elm);
	free(pi);
	return 0;
}