#include <stdlib.h>
#include <stddef.h>

int main(void) {

	int *array = malloc(sizeof(int)*10);
	int *array2 = malloc(sizeof(int)*10);
	int* p = array;
	int* q = array2 + 5;

	ptrdiff_t qp = q - p;  // Invalid. diff1

	ptrdiff_t pq = p - q;  // Invalid. diff2

	if (qp == 5 && pq == -5) {
		free(array);
		free(array2);
	}

	return 0;

}
