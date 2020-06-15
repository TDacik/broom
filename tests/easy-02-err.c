#include <stdlib.h>

/* error: invalid dereference */

int main() {
	int *p;
	return *p; // invalid deref
}
