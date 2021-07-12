#include <stdlib.h>
#include <stdio.h>
#include <alloca.h>

struct sll_node {
        int data;
        struct sll_node *next;
};

void f(struct sll_node **x) {
        (*x) = (*x)->next; 
}

struct sll_node *g(struct sll_node **x) {
        f(x);
        f(x);
        return *x;
}

 

int main() {
        struct sll_node **p_n1 = alloca(sizeof(struct sll_node *));
        struct sll_node **p_n2 = alloca(sizeof(struct sll_node *));
        struct sll_node **p_n3 = alloca(sizeof(struct sll_node *));
        struct sll_node *n1 = (struct sll_node *)malloc(sizeof(struct sll_node));
        struct sll_node *n2 = (struct sll_node *)malloc(sizeof(struct sll_node));
        struct sll_node *n3 = (struct sll_node *)malloc(sizeof(struct sll_node));
        *p_n1 = n1;
        *p_n2 = n2;
        *p_n3 = n3;
        
        n1->data = 1;
        n1->next = n2;
        n2->data = 2;
        n2->next = n3;
        n3->data = 3;
        n3->next = NULL;

        struct sll_node *y = g(p_n1);

        printf("data: %i\n",y->data);

        free(n1);
        free(n2);
        free(n3);

        return 0;
}

