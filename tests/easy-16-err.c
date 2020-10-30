int ok() {
	int a = 4;
	short sa = *((short *)&a);

	return a;
}

int err() {
	int a = 4;
	long long lla = *((long long *)&a); // error

	return a;
}
