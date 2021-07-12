// from https://github.com/gcc-mirror/gcc/blob/master/gcc/testsuite/gcc.dg/tree-ssa/alias-10.c

/* { dg-do compile } */
/* { dg-options "-O2 -fdump-tree-optimized" } */

#include <stdlib.h>

struct a {
	int i;
	int x[2];
	int j;
};

int foo(struct a* a, int i)
{
	a->i = 1;
	a->j = 2;
	a->x[i] = 0; // error if i<-1 and i>2
	return a->i + a->j;
}

/* { dg-final { scan-tree-dump "return 3;" "optimized" } } */

void test_foo()
{
	struct a *a = malloc(sizeof(struct a));
	foo(a, -1);
	free(a);
}

void test_foo1()
{
	struct a *a = malloc(sizeof(struct a));
	foo(a, 1);
	free(a);
}

void test_foo2()
{
	struct a *a = malloc(sizeof(struct a));
	foo(a, 2);
	free(a);
}

void test_foo3()
{
	struct a *a = malloc(sizeof(struct a));
	foo(a, 3); // error
	free(a);
}

int main() {
	test_foo();
	test_foo1();
	test_foo2();
	test_foo3();
}
