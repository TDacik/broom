#include <stdlib.h>

struct q {
	int item0;
	struct p * item1;
	int item2;
};

struct p {
	int item0;
	struct p * item1;
};

int ok() {
	struct p sp = {3, NULL};
	int si = *((int *)&sp);

	return si;
}

int err() {
	struct p sp = {3, NULL};
	int si = ((struct q *)&sp)->item2;

	return si;
}
