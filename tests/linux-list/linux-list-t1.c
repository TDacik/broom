#include <stdlib.h>
#include <stdbool.h>

struct list_head {
    struct list_head *next, *prev;
};

#define LIST_HEAD_INIT(name) { &(name), &(name) }

#define LIST_HEAD(name) \
    struct list_head name = LIST_HEAD_INIT(name)

/*
 * Insert a new entry between two known consecutive entries.
 *
 * This is only for internal list manipulation where we know
 * the prev/next entries already!
 */
static inline void __list_add(struct list_head *new,
                              struct list_head *prev,
                              struct list_head *next)
{
    next->prev = new;
    new->next = next;
    new->prev = prev;
    prev->next = new;
}

/**
 * list_add_tail - add a new entry
 * @new: new entry to be added
 * @head: list head to add it before
 *
 * Insert a new entry before the specified head.
 * This is useful for implementing queues.
 */
static inline void list_add_tail(struct list_head *new, struct list_head *head)
{
    __list_add(new, head->prev, head);
}

struct my_item {
    void                *data;
    struct list_head    link;
};

void append_one(struct list_head *head)
{
    struct my_item *ptr = malloc(sizeof *ptr);
    if (!ptr)
        abort();

    ptr->data = NULL;
    list_add_tail(&ptr->link, head);
}

/*
void traverse(struct list_head *head)
{
    struct my_item *now = (struct my_item *)(
            (char *)head->next - __builtin_offsetof (struct my_item, link)
            );

    while (&now->link != (head)) {
        now = (struct my_item *)(
                (char *)now->link.next - __builtin_offsetof (struct my_item, link)
                );
    }
}
*/

void init_dll(struct list_head *head)
{
    head->prev = head;
    head->next = head;
}

struct list_head* test1()
{
    struct list_head *head=malloc(sizeof(struct list_head));
    init_dll(head);
    append_one(head);
    append_one(head);
    return head;
}

/**
 * @original file: predator regre: test-0156.c
 */
