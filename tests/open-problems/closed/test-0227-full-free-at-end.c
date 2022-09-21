#include <stdlib.h>
#include <verifier-builtins.h>

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
    // allocate shared data
    void *data = malloc(113U);

    // create SLS 2+
    struct item *list = NULL;
    list = append(list, data);
    list = append(list, data);
    while (__VERIFIER_nondet_int())
        list = append(list, data);

    // var-killer kills 'data' at this point

    while (list) {
        struct item *next = list->next;
        // the following statement plugs a memleak
        free(list);
        list = next;
    }
    free(data);
    // return !!data;
}

/**
 * @file test-0227.c
 *
 * @brief leak-less variant of test-0225
 *
 * @attention
 * This description is automatically imported from tests/predator-regre/README.
 * Any changes made to this comment will be thrown away on the next import.
 */
