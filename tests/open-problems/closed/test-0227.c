#include <stdlib.h>
#include <verifier-builtins.h>

/**
 * Why is entailment_limit reached?
 */

struct item {
    struct item *next;
    void *data;
};

static struct item* append(struct item *plist, void *data)
{
    struct item *item = malloc(sizeof *item);
    item->next = plist;
    item->data = data;
    return item;
}

int main()
{
    void *data = malloc(113U);
    struct item *list = NULL;
    list = append(list, data);
    list = append(list, data);
    while (__VERIFIER_nondet_int())
        list = append(list, data);
    free(data);    
}

