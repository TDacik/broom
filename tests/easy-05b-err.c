#include <stdlib.h>

/* error: use after free - dereference of already deleted heap object */

int s(int *p, int flag) {
	if (flag != 1)
		free(p);
	return *p; // use after free if (flag != 1)
}

