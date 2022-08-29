#include <stdlib.h>
#include <verifier-builtins.h>
/**
First working example with shared nodes
 */

struct item {
    struct item *next;
    void *data;
};

void loop(struct item *x)
{
    void *data = malloc(113U);
    while (x!=NULL){
        x->data = data;
        x=x->next;
    }
    free(data);
}