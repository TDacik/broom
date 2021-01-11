// Creating a DLL.
// based on predator-regre test-0054.c !!! without size

#include <stdlib.h>

struct item {
    struct item *next;
    struct item *prev;
};

struct dll {
    // size_t size;
    struct item *beg;
    struct item *end;
};

int dll_empty(struct dll *list)
{
    return !(list->beg);
}

#define DLL_ASSERT_NON_EMPTY(list) \
    assert(!dll_empty(list))

#define DLL_SET_IF_NULL(dst, src) \
    if (!(dst)) dst = (src)

// struct item* alloc_or_die(void)
// {
//     struct item *pi = malloc(sizeof(*pi));
//     if (pi)
//         return pi;
//     else
//         abort();
// }

struct item* alloc_and_zero(void)
{
    struct item *pi = malloc(sizeof(*pi));
    pi->next = NULL;
    pi->prev = NULL;

    return pi;
}

struct dll* create_dll(void)
{
    struct dll* list = malloc(sizeof(*list));;
    struct item *dll = alloc_and_zero();
    struct item *now = dll;
    list->beg = dll;
    list->end = NULL;
    // list->size = 0;

    // NOTE: running this on bare metal may cause the machine to swap a bit
    int i;
    for (i = 1; i; ++i) {
        now->next = alloc_and_zero();
        now->next->prev = now;
        now = now->next;
        list->end = now;
        // list->size += 1;
    }
    return list;
}

struct item* dll_push_back(struct dll *list)
{
    struct item *item = alloc_and_zero();
    if ((item->prev = list->end))
        item->prev->next = item;
    DLL_SET_IF_NULL(list->beg, item);
    list->end = item;
    // list->size ++;
    return item;
}

struct item* dll_push_front(struct dll *list)
{
    struct item *item = alloc_and_zero();
    if ((item->next = list->beg))
        item->next->prev = item;
    list->beg = item;
    DLL_SET_IF_NULL(list->end, item);
    // list->size ++;
    return item;
}

void dll_pop_back(struct dll *list)
{
    DLL_ASSERT_NON_EMPTY(list);

    struct item *item = list->end;
    if ((list->end = item->prev))
        list->end->next = NULL;
    else
        list->beg = NULL;

    // list->size --;
    free(item);
}

void dll_pop_front(struct dll *list)
{
    DLL_ASSERT_NON_EMPTY(list);

    struct item *item = list->beg;
    if ((list->beg = item->next))
        list->beg->prev = NULL;
    else
        list->end = NULL;

    // list->size --;
    free(item);
}

struct item* dll_insert_after(struct dll *list, struct item *item)
{
    struct item *new_item = alloc_and_zero();
    new_item->next = item->next;
    new_item->prev = item;

    if (item->next)
        item->next->prev = new_item;
    else
        list->end = new_item;

    item->next = new_item;

    // list->size ++;
    return new_item;
}

struct item* dll_insert_before(struct dll *list, struct item *item)
{
    struct item *new_item = alloc_and_zero();
    new_item->next = item;
    new_item->prev = item->prev;

    if (item->prev)
        item->prev->next = new_item;
    else
        list->beg = new_item;

    item->prev = new_item;

    // list->size ++;
    return new_item;
}


void dll_remove(struct dll *list, struct item *item)
{
    if (!item)
        return;

    if (item->next)
        item->next->prev = item->prev;
    else
        list->end = item->prev;

    if (item->prev)
        item->prev->next = item->next;
    else
        list->beg = item->next;

    // list->size --;
    free(item);
}

void dll_destroy(struct dll *list)
{
    /* destroy items in reverse order */
    struct item *item = list->end;
    while (item) {
        struct item *prev = item->prev;
        free(item);
        item = prev;
    }

    free(list);
}

int main()
{
    struct item *list = create_dll();

    dll_push_front(list);
    struct item *item = dll_push_back(list);
    item = dll_insert_before(list, item);
    item = dll_insert_after(list, item);
    dll_pop_back(list);

    dll_destroy(list);

    return 0;
}

