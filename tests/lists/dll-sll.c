// Create a SLL based on the node structure of DLL (only next is used). 
// Then traverse the list while setting values of prev (thus creating a DLL). 
// Finally, traverse the list while resetting next (thus creating a reversed SLL).

#include <stdlib.h>

struct item {
    struct item *next;
    struct item *prev;
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

    return pi;
}

struct item* create_item(struct item *end)
{
    struct item *pi = alloc_and_zero();
    pi->next = end;
    return pi;
}

struct item* create_sll(void)
{
    struct item *sll = create_item(NULL);

    // NOTE: running this on bare metal may cause the machine to swap a bit
    int i;
    for (i = 1; i; ++i) {
        sll = create_item(sll);
    }
    return sll;
}

void sll_to_dll(struct item *dll)
{
    while (dll && dll->next) {
        struct item *prev = dll;
        dll = dll->next;
        dll->prev = prev;
    }
}

struct item* dll_to_sll(struct item *dll)
{
    while (dll && dll->next) {
        struct item *next = dll->next;
        dll->next = NULL;
        dll = next;
    }
    return dll;
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

struct item* dll_to_sll2()
{
    struct item *dll = create_dll();
    while (dll && dll->next) {
        struct item *next = dll->next;
        dll->next = NULL;
        dll = next;
    }
    return dll;
}

void destroy_from_end(struct item *dll)
{
    while (dll) {
        struct item *prev = dll->prev;
        free(dll);
        dll = prev;
    }
}

int main()
{
    // create a SLL
    struct item *dll = create_sll();

    // convert the SLL to DLL by completing the 'prev' field
    sll_to_dll(dll);

    // convert the DLL to SLL by zeroing the 'next' field
    dll = dll_to_sll(dll);

    // finally just destroy the list to silence our garbage collector
    destroy_from_end(dll);

    return 0;
}

/**
 * @file test-0061.c
 *
 * @brief conversion of SLL to DLL and vice versa
 *
 *     1. creates a singly-linked list, using the 'next' selector
 *        for biding
 *
 *     2. goes through the list and completes the missing values
 *        of 'prev' selector, in order to obtain a doubly-linked
 *        list
 *
 *     3. goes through the list and zero the 'next' selector
 *        of each node, in order to get a reversed singly-linked
 *        list
 *
 * @attention
 * This description is automatically imported from tests/predator-regre/README.
 * Any changes made to this comment will be thrown away on the next import.
 */
