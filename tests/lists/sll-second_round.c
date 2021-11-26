
// minimal test of singly linked list

#include <stdlib.h>
#include <stdio.h>
#include <alloca.h>
#define TEST

struct sll_item {
    struct sll_item *next;
    int data;
};


void sll_print(struct sll_item *list)
{
    while (list != NULL) {
        printf("%d ",list->data);
        list = list->next;
        printf("%d ",list->data);
        list = list->next;
    }
    printf("\n");
}
