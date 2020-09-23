#include <stdlib.h>

/* multiple errors */

void f(int *p, int *q) {
	free(p);    // precondition - potentially error f1
	int a = *q; // precondition - potentially error f2
}

void g(int *q) {
	int a = *q; // precondition - potentially error g3
	int *p = malloc(sizeof(int));
	free(p);
	f(p, NULL); // error f1 and f2
}

void h() {
	int *p;
	g(p); // error g3, note about errors f1 and f2
}