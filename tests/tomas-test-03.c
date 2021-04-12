#include <stdlib.h>
#include <alloca.h>

void ff(int **pp) {
    *pp = malloc(sizeof(int)); // Tady se muze zdat, ze stara hodnota *pp je junk.
    if (*pp == NULL) abort();
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

    ff(s);  // Junk nevznika, protoze na starou bunku ukazuje t.
            // Kdyby ale tam t=s nebylo, junk vznikne.
    free(*t);
    free(*s);
}
