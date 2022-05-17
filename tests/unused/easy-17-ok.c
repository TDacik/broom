#include <stdlib.h>

struct p {
	int item0;
	struct p * item1;
};

int main() {

	struct p sp = {3, NULL};

	sp.item1 = &sp;                                          //BUG!!!!!
	/* sp.item1 := &sp */

	struct p * p_sp = &sp; // malloc(sizeof(struct p));
	(*p_sp).item1 = (struct p*) &p_sp;
// 	free(p_sp);

	return sp.item0;
}


//assert( op1.var.uid = op2.var.uid && ( () || () ) )

// op1.accessor, op2.accessor
// [],_
// _,[]
// _,last(Ref)