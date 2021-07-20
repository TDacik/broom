#include <stdlib.h>
#include <string.h>

// regression test for overlapping arguments of called functions with
// parameters of function's contract

char * copy5(char * p) {
	char * q = malloc(sizeof(char)*5);
	memcpy(q,p,5);
	return q;
}

char * shallow_copy(char * p) {
	return p;
}

void freed(char * p) {
	free(p);
}

int no_overlap_empty_args() {
	char * str = "Alla";
	char *x = copy5(str);
	free(x);
	return 0;
}

int no_overlap_empty_lhs() {
	char *x = shallow_copy("Alla");
	free(x); // error: freed static object
	return 0;
}

// void overlap_err() {
// 	freed("Alla"); // error: freed static object
// }

// int overlap() {
// 	char *x = copy5("Alla");
// 	free(x);
// 	return 0;
// }
