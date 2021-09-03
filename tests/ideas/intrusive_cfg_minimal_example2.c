#include "intrusive_cfg.h"
#include <stddef.h> /* size_t */
#include <stdlib.h>

#define LIST_CREATE(structure, member) list_create(offsetof(structure, member))
#define LINK_INIT(linkptr, structure, member) \
  link_init(linkptr, offsetof(structure, member))

static link* list_get_link_from_node(list *l, void* node) {
  return (link*) ((size_t) node + l->offset);
}


static link* link_get_next(link* lnk) {
  /* offset from a node pointer to a link structure */
  size_t offset = (size_t) lnk - ((size_t) lnk->prev->next & ~1);
  /* link field for the next node */
  size_t offset_of_next = (size_t) lnk->next & ~1;
  return (link*) (offset_of_next + offset);
}

void link_init(link *lnk, size_t offset) {
  lnk->next = (void*) ((size_t) lnk + 1 - offset);
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


static void link_remove(link *lnk) {
  link_get_next(lnk)->prev = lnk->prev;
  lnk->prev->next = lnk->next;
}


static void list_add_after(list *l, link *link_of_node, void *node, link *previous_link) {
  link_remove(link_of_node);

  link_of_node->prev = previous_link;
  link_of_node->next = previous_link->next;

  link_get_next(previous_link)->prev = link_of_node;
  previous_link->next = node;
}


void list_insert_head(list *l, void* node) {
  link *link = list_get_link_from_node(l, node);
  list_add_after(l, link, node, &l->link);
}

#define TEST1
#ifdef TEST1
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
  
  list* l = LIST_CREATE(person, link);
  list_insert_head(l, p);

  free(p);
  //free(l);

  return 0;
}
#endif
