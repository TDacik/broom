#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


#define DLL_NULL ((dll_item_t *) 0)

typedef struct dll dll_t;
typedef struct dll_item dll_item_t;

struct dll {
    size_t          size;
    dll_item_t      *beg;
    dll_item_t      *end;
};

struct dll_item {
    dll_item_t      *next;
    dll_item_t      *prev;
};
#define DLL_ASSERT_NON_EMPTY(list) \
    assert(!dll_empty(list))

#define DLL_DIE do { \
    /* this call should never return */ \
    dll_die(__FUNCTION__); \
    abort(); \
} while (0)

#define DLL_ZNEW(type) \
    ((type *) calloc(1, sizeof(type)))

#define DLL_SET_IF_NULL(dst, src) \
    if (!(dst)) dst = (src)

void dll_die(const char *msg)
{
    abort();
}

static dll_item_t* create_item(void)
{
    dll_item_t *item = DLL_ZNEW(dll_item_t);
    if (!item)
        DLL_DIE;

    return item;
}

void dll_init(dll_t *list)
{
    memset(list, '\0', sizeof *list);
}

void dll_destroy(dll_t *list)
{
    /* destroy items in reverse order */
    dll_item_t *item = list->end;
    while (item) {
        dll_item_t *prev = item->prev;
        free(item);
        item = prev;
    }

    dll_init(list);
}

int dll_empty(dll_t *list)
{
    return !(list->beg);
}

size_t dll_size(dll_t *list)
{
    return list->size;
}

dll_item_t* dll_beg(dll_t *list)
{
    return list->beg;
}

dll_item_t* dll_end(dll_t *list)
{
    return list->end;
}

dll_item_t* dll_next(dll_item_t *item)
{
    return item->next;
}

dll_item_t* dll_prev(dll_item_t *item)
{
    return item->prev;
}

dll_item_t* dll_push_back(dll_t *list)
{
    dll_item_t *item = create_item();
    if ((item->prev = list->end))
        item->prev->next = item;
    DLL_SET_IF_NULL(list->beg, item);
    list->end = item;
    list->size ++;
    return item;
}

dll_item_t* dll_push_front(dll_t *list)
{
    dll_item_t *item = create_item();
    if ((item->next = list->beg))
        item->next->prev = item;
    list->beg = item;
    DLL_SET_IF_NULL(list->end, item);
    list->size ++;
    return item;
}

void dll_pop_back(dll_t *list)
{
    DLL_ASSERT_NON_EMPTY(list);

    dll_item_t *item = list->end;
    if ((list->end = item->prev))
        list->end->next = DLL_NULL;
    else
        list->beg = DLL_NULL;

    list->size --;
    free(item);
}

void dll_pop_front(dll_t *list)
{
    DLL_ASSERT_NON_EMPTY(list);

    dll_item_t *item = list->beg;
    if ((list->beg = item->next))
        list->beg->prev = DLL_NULL;
    else
        list->end = DLL_NULL;

    list->size --;
    free(item);
}

dll_item_t* dll_insert_after(dll_t *list, dll_item_t *item)
{
    dll_item_t *new_item = create_item();
    new_item->next = item->next;
    new_item->prev = item;

    if (item->next)
        item->next->prev = new_item;
    else
        list->end = new_item;

    item->next = new_item;

    list->size ++;
    return new_item;
}

dll_item_t* dll_insert_before(dll_t *list, dll_item_t *item)
{
    dll_item_t *new_item = create_item();
    new_item->next = item;
    new_item->prev = item->prev;

    if (item->prev)
        item->prev->next = new_item;
    else
        list->beg = new_item;

    item->prev = new_item;

    list->size ++;
    return new_item;
}


void dll_remove(dll_t *list, dll_item_t *item)
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

    list->size --;
    free(item);
}
