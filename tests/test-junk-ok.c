#include <stdlib.h>
#include <alloca.h>

void ff(int **pp) {
    *pp = malloc(sizeof(int)); // here it may seem that the old value of *pp is junk
    **pp = 1;
    return;
}

int main() {
    int **s, **t;
    t = alloca(sizeof(int*));
    s = alloca(sizeof(int*));
    *s = malloc(sizeof(int));
    if (*s == NULL) abort();
    **s = 0;
    *t = *s;         

    ff(s);  // No junk, because t points to the old cell.
            // But if t=s were not there, junk will be. 
    free(*t);
    free(*s);
}
