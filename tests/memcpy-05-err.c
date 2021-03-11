#include <string.h>
#include <alloca.h>

struct point {
	int x;
	int y;
	int z;
};

int main() {
	struct point *p = alloca(sizeof(struct point));
	p->x = 3;
	p->y = 4;
	p->z = 5;
	int c = 2*sizeof(int);
	memcpy(p, &(p->y), c); // error: memcpy overlap
	return p->x + p->y + p->z;
}
