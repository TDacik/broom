#include<stdlib.h>

int main() {
	char *p = "string";
	//char q[] = "string";
	//p = q;
	if (p[1]=='t')
		malloc(4);
	return 0;
}