#include <string.h>
#include <alloca.h>


int main() {
	char *from = "abcd";
	char *from1 = from + 3;
	void *to = alloca(10*sizeof(char));
	memcpy(to,from1,3);

	return 0;
}
