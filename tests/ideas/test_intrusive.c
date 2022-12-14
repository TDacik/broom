//===================================
// MIT License
//
// Copyright (c) 2010 by Patrick Wyatt
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.
//===================================

#include "minunit.h"
#include "intrusive.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int tests_run = 0;

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

char* smoke_test_1() {
  person *p = person_create("Robbie", 190);
  person *p2 = person_create("Trunky", 1);
  
  list* l = LIST_CREATE(person, link);
  list_insert_head(l, p);
  list_insert_head(l, p2);

  person *phead = (person*) list_head(l);
  person *next = (person*) link_next(&phead->link);

  MU_ASSERT("head of the list is Trunky", strcmp("Trunky", phead->name) == 0);
  MU_ASSERT("second in the list is Robbie", strcmp("Robbie", next->name) == 0);

  MU_ASSERT("head is linked before unlink", link_is_linked(&phead->link));
  link_unlink(&phead->link);
  MU_ASSERT("head is not linked after unlink", !link_is_linked(&phead->link));

  phead = (person*) list_head(l);
  MU_ASSERT("head of the list is Robbie", strcmp("Robbie", phead->name) == 0);

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

  MU_ASSERT("head of the list is Robbie", strcmp("Robbie", phead->name) == 0);
  MU_ASSERT("second in the list is Trunky", strcmp("Trunky", next->name) == 0);

  person *ptail = (person*) list_tail(l);
  person *nextt = (person*) link_next(&ptail->link);

  
  MU_ASSERT("tail of the list is Trunky", strcmp("Trunky", ptail->name) == 0);
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
