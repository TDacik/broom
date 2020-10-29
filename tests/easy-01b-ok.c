#include <stdlib.h>

struct s {
	int a, b, c;
};

int main() {
	struct s *s;
	int *q, *r;
	int tmp = 0;

	q = &(s->b);
	r = &(s->b);
	if  (q != r) { tmp = s->a; } // error not reachable
	return tmp;
}
