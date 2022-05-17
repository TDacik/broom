#include <stdio.h>

int set(int *a, int *b) {
	*a = *a + 1;
	*b = *b + 2;          // if (a=b) *b = *a + 1 + 2
	return *a + *b;       // if (a=b) ret = *a + *a + 1 + 1 + 2 + 2
}

/*
int t1() {
	int x = 0;
	int y = set(&x, &x);  // x=1... x=3,y=6
	printf("x=%d,y=%d\n", x, y);
	x = set(&x, &x);      // x=4... x=6... x=12
	printf("x=%d,y=%d\n", x, y);
	return x;
}
*/

int t2() {
	int x = 0;
	int *px = &x;
	int y = set(px, px);  // x=1... x=3,y=6
	x = set(px, px);      // x=4... x=6... x=12
	return x;
}
