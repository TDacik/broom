#include <stdlib.h>

struct i_node {
	int i;
};

struct node {
	int i;
	int j;
};


struct node* init_and_get(struct i_node *a) {
	a->i=3;
	a = malloc(sizeof(struct node));
	a->i=5;
	((struct node *)a)->j=6;
	return (struct node *)a;
}

int main() {
	struct i_node *p = malloc(sizeof(struct i_node));
	struct node *q = init_and_get(p);
	free(p);
	free(q);
	return 0;
}