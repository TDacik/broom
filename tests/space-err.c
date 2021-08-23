#include<stdlib.h>
#include<limits.h>

// m64 : 9223372036854775808
// m32 : 2147483648

int main() {

	char * p1 = malloc(9223372036854775806L); // half the memory space minus 1 (for NULL)
	if (p1==NULL) return 1;
	free(p1);
	char * p2 = malloc(9223372036854775806L); // half the memory space plus 1
	if (p2==NULL) return 1;
	free(p2);
	char * p3 = malloc(9223372036854775806L); // half the memory space plus 1
	if (p3==NULL) return 1;
	free(p3);
	*p1='a'; // error
	return 0;
}
