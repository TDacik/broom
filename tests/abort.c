#include <stdlib.h>

int *g;

int aborted() {
	g = malloc(sizeof(int));
	abort();
	return *g;
}

int main() {
	return aborted();
}