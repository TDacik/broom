//#include "intrusive.h"
//#include <stddef.h> /* size_t */ 
#include <stdlib.h>

#include <stddef.h> /* size_t, offsetof */
#define LIST_CREATE(structure, member) list_create(offsetof(structure, member))
#define LINK_INIT(linkptr, structure, member) \
  link_init(linkptr, offsetof(structure, member))

// All nodes (=next) must be allocated on (at least) two-byte boundaries
// because the low bit is used as a sentinel to signal end-of-list.
typedef struct link {
  struct link *prev; 
  void *next;
} link;

typedef struct list {
  struct link link;
  size_t offset;
} list;

static link* link_get_next(link* l);
static void link_remove(link *lnk);
static void list_add_before(list *l, link *link_of_node, void *node, link *next_link);
static void list_add_after(list *l, link *link_of_node, void *node, link *previous_link);
static link* list_get_link_from_node(list *l, void* node);

void link_init(link *l, size_t offset);
void* link_prev(link *lnk); 
void* link_next(link *lnk);
int link_is_linked(link *lnk);
void link_unlink(link *lnk);

list* list_create(size_t offset);
void list_insert_head(list *l, void* node);
void list_insert_tail(list *l, void* node);
void* list_head(list *l);
void* list_tail(list *l);

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

/* main test */
typedef struct {
  int id;  
  link link;
} person;

person* person_create(int id) {
  person *p = malloc(sizeof(person));
  if (p) {
    p->id = id;
    LINK_INIT(&p->link, person, link);
  }
  return p;
}

int test_1() {
  person *p = person_create(1); //Robie
  person *p2 = person_create(2); //Trunky
  
  list* l = LIST_CREATE(person, link);
  list_insert_head(l, p);
  list_insert_head(l, p2);

  person *phead = (person*) list_head(l);
  person *next = (person*) link_next(&phead->link);

  /*MU_ASSERT("head of the list is Trunky", strcmp("Trunky", phead->name) == 0);*/
  assert(phead->id==2);
  /*MU_ASSERT("second in the list is Robbie", strcmp("Robbie", next->name) == 0);*/
  assert(next->id==1);
  /* MU_ASSERT("head is linked before unlink", link_is_linked(&phead->link)); */
  assert(link_is_linked(&phead->link));
  link_unlink(&phead->link);
  /*MU_ASSERT("head is not linked after unlink", !link_is_linked(&phead->link));*/
  assert(!link_is_linked(&phead->link));
  phead = (person*) list_head(l);
  /*MU_ASSERT("head of the list is Robbie", strcmp("Robbie", phead->name) == 0);*/
  assert(phead->id==1);
  free(p);
  free(p2);
  free(l);

  return 0;
}

int test_2(list *l) {
  person *p = person_create(1); //Robie
  person *p2 = person_create(2); //Trunky
  
  list_insert_head(l, p);
  list_insert_head(l, p2);

  person *phead = (person*) list_head(l);
  person *next = (person*) link_next(&phead->link);

  /*MU_ASSERT("head of the list is Trunky", strcmp("Trunky", phead->name) == 0);*/
  assert(phead->id==2);
  /*MU_ASSERT("second in the list is Robbie", strcmp("Robbie", next->name) == 0);*/
  assert(next->id==1);
  /* MU_ASSERT("head is linked before unlink", link_is_linked(&phead->link)); */
  assert(link_is_linked(&phead->link));
  link_unlink(&phead->link);
  /*MU_ASSERT("head is not linked after unlink", !link_is_linked(&phead->link));*/
  assert(!link_is_linked(&phead->link));
  phead = (person*) list_head(l);
  /*MU_ASSERT("head of the list is Robbie", strcmp("Robbie", phead->name) == 0);*/
  assert(phead->id==1);
  free(p);
  free(p2);

  return 0;
}


