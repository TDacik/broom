#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
extern unsigned __VERIFIER_nondet_unsigned(void);

int unsign(void) {
	unsigned size = __VERIFIER_nondet_unsigned();
	int*p = malloc(size);

	if (size>=0)
		free(p);
	return 0;
}

int unsign_zero(void) {
	unsigned size = __VERIFIER_nondet_unsigned();
	int*p = malloc(size);

	if (size>0)
		free(p); // memory leak if size==0
	return 0;
}

int sign(void) {
	int size = __VERIFIER_nondet_int();
	int*p = malloc(size);

	if (size>=0)
		free(p); // memory leak - not detected!
	return 0;
}
