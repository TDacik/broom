#include <stdlib.h>

int main() {
	int *a = malloc(sizeof(int));
	*a = 5;
	free(a);
	return 0;
}
