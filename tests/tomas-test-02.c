#include <stdlib.h>

int f(void) {
  void *x,*y;
  x = malloc(8);
  free(x);
  y = malloc(8);
  if (x==y) {free(y); return 1;}
  else {free(y); return 0;}
}  


