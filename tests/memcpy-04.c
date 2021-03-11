// copy into structure
#include <string.h>
#include <stdio.h>
#include <alloca.h>

struct bus {
	int x;
	struct bus* y;
};

struct krab {
	char x;
	struct bus y;
	int z;
};


int main() {
	struct krab *socha = alloca(sizeof(struct krab));
	socha->x = 'a';
	socha->y.x = 5;
	socha->y.y = 0;
	socha->z = 4;
	struct krab *david = alloca(sizeof(struct krab));;
	struct bus *trup = alloca(sizeof(struct bus));

	memcpy(trup, &(socha->y), sizeof(trup));
	printf("%d ", trup->x);

	memcpy(&(david->y), &(socha->y), sizeof(david->y));
	printf("%d ", david->y.x);

	return trup->x + david->y.x;
}
