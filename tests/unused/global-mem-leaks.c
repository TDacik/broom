#include <stdlib.h>

/* warning: memory leak detected while destroying a static variable */

int *g;

void alloc_glob() {
	g = malloc(sizeof(int));
}

int aborted() {
	abort();
	return *g;
}

int glob_abort() {
	alloc_glob();
	aborted(); // memory leak
	return *g;
}

void glob_exit() {
	g = malloc(sizeof(int));
	exit(1); // memory leak
}

void glob_Exit() {
	g = malloc(sizeof(int));
	_Exit(1); // memory leak
}

int main() {
	alloc_glob();
	return 0; // memory leak
}

/* warning: memory leak detected while assigning a static variable */

void glob_assign() {
	alloc_glob();
	alloc_glob(); // memory leak
}
