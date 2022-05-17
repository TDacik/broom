// Creating a DLL and destroying it forwards, then creating another one and deleting it backwards.

// based on predator-regre/test-0059.c

#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

struct item {
    struct item *next;
    struct item *prev;
    int data;
};

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
    struct item *pi = malloc(sizeof(*pi)); // alloc_or_die();
    pi->next = NULL;
    pi->prev = NULL;
    pi->data = 0;

    return pi;
}

struct item* create_item(struct item *end)
{
    struct item *pi = alloc_and_zero();
    pi->prev = end;
    end->next = pi;
    return pi;
}

struct item* create_dll(void)
{
    struct item *dll = alloc_and_zero();
    struct item *now = dll;

    // NOTE: running this on bare metal may cause the machine to swap a bit
    int i;
    for (i = 1; i; ++i) {
        now->next = alloc_and_zero();
        now->next->prev = now;
        now = now->next;
    }
    return dll;
}

void set_data(struct item *dll)
{
    // int i = 0;
    struct item *node = dll;
    while (node) {
        node->data = __VERIFIER_nondet_int();// i++;
        node = node->next;
    }
}

void destroy_from_beg(struct item *dll)
{
    while (dll) {
        struct item *next = dll->next;
        free(dll);
        dll = next;
    }
}

int main()
{
    // create a DLL
    struct item *dll = create_dll();

    set_data(dll);

    // destroy the list, starting from the "begin"
    destroy_from_beg(dll);

    return 0;
}
