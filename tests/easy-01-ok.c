struct sll_node {
	struct sll_node *next;
};

int main() {
	struct sll_node *p;
	struct sll_node **q; 
	q=&(p->next);           // no error, only pointer arithmetic
	return 0;
}