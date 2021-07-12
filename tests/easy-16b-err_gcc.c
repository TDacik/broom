#include <stdlib.h>
#include <alloca.h>

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
	struct p *p_sp = alloca(sizeof(struct p));
	p_sp->item0 = 3;
	p_sp->item1 = NULL;
	int si = *((int *)p_sp);

	return si;
}

int err() {
	struct p *p_sp = alloca(sizeof(struct p));
	p_sp->item0 = 3;
	p_sp->item1 = NULL;
	int si = ((struct q *)p_sp)->item2;

	return si;
}
