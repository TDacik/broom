#include <stdlib.h>
#include <stddef.h>

int main(void) {

	int *array = malloc(sizeof(int)*10);
	int* p = array;
	int* q = array + 5;

	ptrdiff_t qp = q - p;  // Valid. diff1 is 5

	ptrdiff_t pq = p - q;  // Valid. diff2 is -5

	if (qp == 5 && pq == -5)
		free(array);

	return 0;

}
