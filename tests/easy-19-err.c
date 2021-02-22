#include <stdlib.h>
//void __VERIFIER_plot(const char *name, ...);

int main() {
	int *p = NULL;
	for (int i = 0; i < 2; ++i) {
		int a;
		//__VERIFIER_plot("i");
		if (i == 1 && a != 10) // condition depends on uninitialized value
			return *p;
		a = 10;
	}
	return 0;
}
