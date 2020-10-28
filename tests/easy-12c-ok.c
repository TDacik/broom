#include <stdlib.h>

int b = 8;

int main(void) {
	int *a = &b;
	a = alloca(sizeof(int));
	// int *b = a;
	a = NULL;

    return 0;
}

// regression test for not reporting memory leak from stack/static storage
