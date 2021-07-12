#include <stdlib.h>
#include <alloca.h>
#include <stdio.h>
#include <math.h>

struct dll {
    struct dll *next; 
    struct dll *prev;
//    int i;
};

struct dll* alloc_dll (struct dll **lst) {
    struct dll* fst = malloc (sizeof(struct dll));
    struct dll *d = fst;
    d->prev = NULL;
//    d->i = 1;
    d->next = malloc (sizeof(struct dll));
    d->next->prev = d;
    d = d->next;
//    d->i = 2;
    d->next = malloc (sizeof(struct dll));
    d->next->prev = d;
    d = d->next;
//    d->i=3;
    d->next = NULL;
    *lst = d;
    return fst;
}

void trans(struct dll* s, struct dll *e) {
    struct dll* i;
    struct dll* j;
    for(i = s; i != NULL; i = i->next) ;
//        printf("%d\n",i->i);
    for(j = e; j != NULL; j = j->prev) ;
//        printf("%d\n",j->i);
}

void insertDLS(struct dll* l) {
	while (random()) {
		struct dll* x=l;
		while(x && random()) {
		x = x->next;
		}
		if (x) {
			struct dll* y =malloc(sizeof(struct dll));
			y->next = x->next;
			y->prev = x;
			x->next = y;
			if (y->next) y->next->prev = y;
		}

	}
}


int main() {
    struct dll **p_lst = alloca(sizeof(struct dll *));
    struct dll *fst = alloc_dll(p_lst);
    trans(fst, *p_lst);
    for(struct dll *i = fst->next; i != NULL; i = i->next) 
        free(i->prev);
    free(*p_lst);
    return 0;
}
