#include <stdlib.h>

/* error: dereferencing object of size << sizeOfTarget << B out of bounds */

int main(int argc, char **argv) {
	char *a;
	if (argc == 1)
    	a = argv[1]; // invalid deref
    return 0;
}
