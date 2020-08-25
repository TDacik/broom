#include <stdlib.h>
#include <stdint.h>

/* error: free called on non-pointer value */

int main() {
	intptr_t ret = 1;
	free((void*)ret); // invalid free
	return ret;
}
