#include <stdlib.h>

/* error: dereference of NULL value */

int s(int *p) {
	int a;
	if (p == NULL)
		a = *p; // invalid deref if (p == NULL)
	else
		a = 0;
	return a;
}
