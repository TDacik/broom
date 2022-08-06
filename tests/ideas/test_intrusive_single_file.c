// SPDX-License-Identifier: MIT
// based on test_intrusive.c
// because our tool does not support a strings, the corresponding MU_ASSERT
// calls are commented out


#include "minunit.h"
#include "intrusive-list-person.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//-----------------------------------------------------------------------------
void link_init(link *lnk, size_t offset) {
  lnk->next = (void*) ((size_t) lnk + 1 - offset);
  lnk->prev = lnk;
}

void* link_prev(link *lnk) {
  void* node = lnk->prev->prev->next;
  if ((size_t) node & 1)
    return NULL;
  return node;
}

void* link_next(link *lnk) {
  if ((size_t) lnk->next & 1)
    return NULL;
  return lnk->next;
}

int link_is_linked(link *lnk) {
  return lnk->prev != lnk;
}

void link_unlink(link *lnk) {
  link_remove(lnk);

  // end of the list with no offset
  lnk->next = (void*) ((size_t) lnk + 1);
  lnk->prev = lnk;
}

list* list_create(size_t offset) {
  list *l = malloc(sizeof(list));
  if (l) {
    l->offset = offset;
    link_init(&l->link, offset);
  }
  return l;
}

void list_insert_head(list *l, void* node) {
  link *link = list_get_link_from_node(l, node);
  list_add_after(l, link, node, &l->link);
}

void list_insert_tail(list *l, void* node) {
  link *link = list_get_link_from_node(l, node);
  list_add_before(l, link, node, &l->link);
}

void* list_head(list *l) {
  return link_next(&l->link); 
}

void* list_tail(list *l) {
  return link_prev(&l->link);
}

static link* link_get_next(link* lnk) {
  /* offset from a node pointer to a link structure */
  size_t offset = (size_t) lnk - ((size_t) lnk->prev->next & ~1);
  /* link field for the next node */
  size_t offset_of_next = (size_t) lnk->next & ~1;
  return (link*) (offset_of_next + offset);
}

static void link_remove(link *lnk) {
  link_get_next(lnk)->prev = lnk->prev;
  lnk->prev->next = lnk->next;
}

static void list_add_before(list *l, link *link_of_node, void *node, link *next_link) {
  link_remove(link_of_node);

  link_of_node->prev = next_link->prev;
  link_of_node->next = link_of_node->prev->next;

  next_link->prev->next = node;
  next_link->prev = link_of_node;
}

static void list_add_after(list *l, link *link_of_node, void *node, link *previous_link) {
  link_remove(link_of_node);

  link_of_node->prev = previous_link;
  link_of_node->next = previous_link->next;

  link_get_next(previous_link)->prev = link_of_node;
  previous_link->next = node;
}

static link* list_get_link_from_node(list *l, void* node) {
  return (link*) ((size_t) node + l->offset);
}

//-----------------------------------------------------------------------------

// https://github.com/robbiev/coh-linkedlist

int tests_run = 0;

person* person_create(char *name, int weight) {
  person *p = malloc(sizeof(person));
  if (p) {
    p->name = name;
    p->weight = weight;
    LINK_INIT(&p->link, person, link);
  }
  return p;
}

char* smoke_test_1() {
  person *p = person_create("Robbie", 190);
  person *p2 = person_create("Trunky", 1);
  
  list* l = LIST_CREATE(person, link);
  list_insert_head(l, p);
  list_insert_head(l, p2);

  person *phead = (person*) list_head(l);
  person *next = (person*) link_next(&phead->link);

//   MU_ASSERT("head of the list is Trunky", strcmp("Trunky", phead->name) == 0);
//   MU_ASSERT("second in the list is Robbie", strcmp("Robbie", next->name) == 0);

  MU_ASSERT("head is linked before unlink", link_is_linked(&phead->link));
  link_unlink(&phead->link);
  MU_ASSERT("head is not linked after unlink", !link_is_linked(&phead->link));

  phead = (person*) list_head(l);
//   MU_ASSERT("head of the list is Robbie", strcmp("Robbie", phead->name) == 0);

  free(p);
  free(p2);
  free(l);

  return 0;
}

char* smoke_test_2() {
  person *p = person_create("Robbie", 190);
  person *p2 = person_create("Trunky", 1);
  
  list* l = LIST_CREATE(person, link);
  list_insert_tail(l, p);
  list_insert_tail(l, p2);

  person *phead = (person*) list_head(l);
  person *next = (person*) link_next(&phead->link);

//   MU_ASSERT("head of the list is Robbie", strcmp("Robbie", phead->name) == 0);
//   MU_ASSERT("second in the list is Trunky", strcmp("Trunky", next->name) == 0);

  person *ptail = (person*) list_tail(l);
  person *nextt = (person*) link_next(&ptail->link);

  
//   MU_ASSERT("tail of the list is Trunky", strcmp("Trunky", ptail->name) == 0);
  MU_ASSERT("tail+1 of the list is NULL", !nextt); 

  person *prev = (person*) link_prev(&ptail->link);
  person *prev2 = (person*) link_prev(&prev->link);

  MU_ASSERT("tail-1 of the list is NOT NULL", prev); 
  MU_ASSERT("tail-2 of the list is NULL", !prev2); 

  free(p);
  free(p2);
  free(l);

  return 0;
}

char* all_tests() {
  MU_RUN_TEST(smoke_test_1);
  MU_RUN_TEST(smoke_test_2);
  return 0;
}

int main(int argc, char *argv[]) {
  char *result = all_tests();
  if (result) {
    printf("FAILED: %s\n", result);
  } else {
    printf("ALL TESTS PASSED\n");
  }
  printf("Tests run: %d\n", tests_run);

  return result != 0;
}
