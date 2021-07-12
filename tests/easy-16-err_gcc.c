#include <alloca.h>

int ok() {
	int *pa = alloca(sizeof(int));
	*pa = 4;
	short sa = *((short *)pa);

	return *pa;
}

int err() {
	int *pa = alloca(sizeof(int));
	*pa = 4;
	long long lla = *((long long *)pa); // error

	return *pa;
}
