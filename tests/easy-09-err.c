#include <stdlib.h>

/* warning: memory leak detected while trashing return value */

int main() {
	malloc(sizeof(char)); // memory leak no destination
	return 0;
}
