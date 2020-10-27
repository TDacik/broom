// from https://github.com/gcc-mirror/gcc/blob/master/gcc/testsuite/gcc.dg/tree-ssa/alias-10.c

/* { dg-do compile } */
/* { dg-options "-O2 -fdump-tree-optimized" } */

struct {
	int i;
	int x[2];
	int j;
} a;

int foo(int i)
{
	a.i = 1;
	a.j = 2;
	a.x[i] = 0; // error if i<-2 and i>3
	return a.i + a.j;
}

/* { dg-final { scan-tree-dump "return 3;" "optimized" } } */

void test_foo()
{
	foo(-1);
}

void test_foo1()
{
	foo(1);
}

void test_foo2()
{
	foo(2);
}

void test_foo3()
{
	foo(3); // error
}

int main() {
	test_foo();
	test_foo1();
	test_foo2();
	test_foo3();
}
