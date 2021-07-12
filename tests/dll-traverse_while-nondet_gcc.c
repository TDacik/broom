// Creating a DLL and destroying it forwards, then creating another one and deleting it backwards.

#include <stdlib.h>
#include <alloca.h>
extern int __VERIFIER_nondet_int(void);

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


struct item* create_dll(void)
{
    struct item *dll = alloc_and_zero();
    struct item *now = dll;

    // NOTE: running this on bare metal may cause the machine to swap a bit
    int i;
    while(__VERIFIER_nondet_int()) {
        now->next = alloc_and_zero();
        now->next->prev = now;
        now = now->next;
    }
    return dll;
}

struct item* fast_forward_core(struct item *dll)
{
    struct item *next;
    while ((next = dll->next)) {
        dll = next;
    }

    return dll;
}

void fast_forward(struct item **pDll)
{
    *pDll = fast_forward_core(*pDll);
}

void traverse_from_beg(struct item *dll)
{
    struct item *node = dll;
    while (node) {
        node = node->next;
    }
}

void traverse_from_end(struct item *dll)
{
    struct item **p_node = alloca(sizeof(struct item *));
    *p_node = dll;
    // jump to the "end"
    fast_forward(p_node);
    struct item *node = *p_node;
    while (node) {
        node = node->prev;
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
    // create a DLL
    struct item *dll = create_dll();

    traverse_from_beg(dll);

    // destroy the list, starting from the "begin"
    destroy_from_beg(dll);
    
    void* p = dll->next; // error

//     acquire a fresh instance of DLL
//     dll = create_dll();
// 
//     jump to the "end"
//     fast_forward(&dll);
// 
//     destroy the list, starting from the "end"
//     destroy_from_end(dll);

    return 0;
}

/**
 * @file test-0059.c
 *
 * @brief forward/backward destruction of DLL
 *
 * @attention
 * This description is automatically imported from tests/predator-regre/README.
 * Any changes made to this comment will be thrown away on the next import.
 */
