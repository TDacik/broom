#include <stdlib.h>

/* error: dereferencing 0-object */

int main() {
	int *p = malloc(0);
	int ret = *p; // invalid deref
	free(p);
	return ret;
}
