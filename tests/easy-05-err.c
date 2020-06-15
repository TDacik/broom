#include <stdlib.h>

/* error: use after free - dereference of already deleted heap object */

int main() {
	int *p = malloc(sizeof(p));
	free(p);
	return *p; // use after free
}

