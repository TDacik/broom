/**
 * Traversal of Singly-linked nested lists - Why is the analysis failing?
 * 
 * 
 */

#include <stdlib.h>
#include <verifier-builtins.h>

struct node {
    struct node *next;
    struct internal_node *nested_node;
};

struct internal_node{
    struct internal_node *next;
};


void inner_loop(struct internal_node *nested_list){
    while(nested_list!=NULL){
        nested_list=nested_list->next;
    } 
}


void loop(struct node *list){
    while(list!=NULL){
        struct internal_node *nested_list = list->nested_node;
        inner_loop(nested_list);
        list=list->next;
    }
}
