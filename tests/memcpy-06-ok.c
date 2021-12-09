#include <string.h>
#include <alloca.h>


int main() {
	char *from = "abc";
	void *to = alloca(10*sizeof(char));
	memcpy(to,from,4);

	return 0;
}
