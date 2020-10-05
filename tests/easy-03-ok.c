#include <stdlib.h>

void s() {
	int *p = malloc(0);
	free(p);
}
