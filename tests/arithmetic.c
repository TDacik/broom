
int f(int x,_Bool a) {
	if (a) {
		int y=x+1;
		if(y>0)
			return 0;
	}
	return 1;
}