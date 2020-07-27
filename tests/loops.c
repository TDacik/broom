struct dll_node {
	struct dll_node *next;
	struct dll_node *prev;
	int elmt;
};


void del-doublestar(dll_node **listP, int value)
{ 
	dll_node *currP, *prevP;
	prevP=0;
	for (currP=*listP; currP!=0; prevP=currP, currP=currP->next) {
		if (currP->elmt==value) { /* Found it. */
			if (prevP==0) *listP=currP->next;
			else prevP->next=currP->next;
			free(currP);
		} 
	} 
}

struct sll_node {
	struct sll_node *next;
};


void traverse-circ(struct sll_node *c) {
	struct sll_node *h;
	h=c; 
	c=c->next;
	while (c!=h) 
	{ 
		c=c->next;
	}
}


//{ls(x, nil)}
void list-reverse(struct sll_node *x) {
	struct sll_node *a = nil;
	while(x != nil)
	//{ls(x, nil) * ls(a, nil)}
	{
		struct sll_node *b = x->next;
		x->next = a;
		a = x;
		w = b;
	}
	x = w;
}
//{ls(x, nil)}


//{ls(x, nil) /\ u = x}
sll_node* list-copy(struct sll_node *x) {
	struct sll_node *s = malloc(sizeof(struct sll_node));
	struct sll_node *r = s;
	while(x != nil)
	//{ls(u, x) * ls(x, nil) * ls(r,s) * s |-> _}
	{
		struct sll_node *t = = malloc(sizeof(struct sll_node));
		// t.data := x.data; not modelled
		s->next = t;
		s = t;
		y = x->next;
		x = y;
	}
	s->next = nil;
	return s;
}
//{ls(u, x) * ls(r, nil)}