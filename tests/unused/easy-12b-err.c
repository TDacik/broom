#include <stdlib.h>

/* error: dereference of non-existing non-heap object */

int main(void) {
	int b = -1;
	int *a_ptr =&b;
	for (int i = 0; i < 2; ++i) {
		int a;
		int *x = &a;
		a = *a_ptr; // invalid deref if i = 1
		a_ptr = &a;
	} // end of scope for 'a'

    return 0;
}
