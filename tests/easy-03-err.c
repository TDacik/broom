#include <stdlib.h>

/* error: dereferencing 0-object */

int s() {
	int *p = malloc(0);
	int ret = *p; // invalid deref
	free(p);
	return ret;
}

int main() {
	return s(); // note about error from s()
}
