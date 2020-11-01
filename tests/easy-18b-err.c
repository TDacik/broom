
/* error: dereferencing object of size << sizeOfTarget << B out of bounds */

int a[3] = {0,1,2};

int foo(int i) {
	return a[i]; // error if i < 0 or i > 2
}

int foo_plus() {
	return foo(3); // error
}

int foo_ok() {
	return foo(2);
}

int foo_minus() {
	return foo(-2); // error
}

int main() {
	return foo_ok() + foo_minus(); // error from 2nd fnc
}
