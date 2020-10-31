// test case for array dereferencing

/* error: dereferencing object of size << sizeOfTarget << B out of bounds */

short m[4][4][4];

int p[4] = {0,1,2,3};

int err_plus() {
	return p[4]; // error
}

int err_minus_one() {
	return p[-1]; // error
}

int err_minus() {
	return p[-2]; // error
}

int ok() {
	return p[2];
}

int main() {
	int idx = 2;
	m[0][0][0] = 1;
	m[3][idx][1] = 5;
	return (int) m[3][2][1];
}
