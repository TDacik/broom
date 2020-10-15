#include <stdlib.h>

int main(void) {
	int *a = alloca(sizeof(int));
	// int *b = a;
	a = NULL;

    return 0;
}
