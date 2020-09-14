struct sll_node {
	struct sll_node *next;
};

struct sll_node* f(struct sll_node *x)
{
	x = x->next;
	return x;
}

void g(struct sll_node *x)
{
	x = f(x);
	x = f(x);
}
