
// minimal test of singly linked list

#include <stdlib.h>
#include <stdio.h>
#include <alloca.h>
#define TEST

struct sll_item {
    struct sll_item *next;
    int data;
};

// insert first
void sll_insert(struct sll_item **plist, int data)
{
    struct sll_item *p = malloc(sizeof(struct sll_item));
    if (!p)
        abort();
    p->data = data;
    p->next = (*plist);
    (*plist) = p;
}

// in-place list reversal
struct sll_item *sll_reverse(struct sll_item *list)
{
    struct sll_item *prev = NULL;
    struct sll_item *next;

    while (list) {
        next = list->next;
        list->next = prev;
        prev = list;
        list = next;
    }
    return prev;
}

void sll_print(struct sll_item *list)
{
    while (list != NULL) {
        printf("%d ",list->data);
        list = list->next;
    }
    printf("\n");
}

// delete all items
void sll_clear(struct sll_item **plist)
{
    struct sll_item *p = (*plist);
    while (p != NULL) {
        struct sll_item *next = p->next;
        free(p);
        p = next;
    }
    (*plist) = NULL;
}

#ifdef TEST
int main(void)
{
    struct sll_item **p_list = alloca(sizeof(struct sll_item *));
    *p_list = NULL;

    sll_insert(p_list, 1);
    sll_insert(p_list, 2);
    sll_insert(p_list, 3);

    sll_print(*p_list);

    *p_list = sll_reverse(*p_list);

    sll_print(*p_list);

    sll_clear(p_list);

    return 0;
}
#endif
