// SPDX-License-Identifier: MIT
// based on test_intrusive.c


#include <stddef.h> /* size_t, offsetof */
#include <stdio.h>
#include <stdlib.h>

typedef struct link {
  struct link *prev; 
  void *next;
} link;


#define LINK_INIT(linkptr, structure, member) \
  link_init(linkptr, offsetof(structure, member))

//-----------------------------------------------------------------------------
void link_init(link *lnk, size_t offset) {
  lnk->next = (void*) ((size_t) lnk + 1 - offset);
  lnk->prev = lnk;
}


typedef struct {
  int weight;
  char *name;
  link link;
} person;

person* person_create(char *name, int weight) {
  person *p = malloc(sizeof(person));
  if (p) {
    p->name = name;
    p->weight = weight;
    LINK_INIT(&p->link, person, link);
  }
  return p;
}
