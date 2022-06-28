#include <stdlib.h>

/* error: dereference of non-existing non-heap object */

int main(void) {
	int *a_ptr = NULL;
	{
		int a = 3;
		a_ptr = &a;
	} // end of scope for 'a'

    return *a_ptr; // invalid deref
}
