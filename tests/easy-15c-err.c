#include <stdlib.h>

int s() {
	int *p = malloc(sizeof(int));
	int *q = malloc(sizeof(int));

//	if ((intptr_t)p-(intptr_t)q) // optimized in gcc to  p!=q

// 	if (((intptr_t)p-(intptr_t)q)>0)
// 		return 1;
// 	else return 0;

	return (intptr_t)p-(intptr_t)q; // 2x memory leak
}
