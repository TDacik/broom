#include <stdlib.h>

/* error: free called on non-pointer value */

int main() {
	int ret = 1;
	free(ret); // invalid free
	return ret;
}
