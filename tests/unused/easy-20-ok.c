int s() {
	int x = 3;
	int *px;
	px = &x;
	*px = 5;
	return x;
}
