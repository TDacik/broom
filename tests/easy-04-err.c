#include <stdlib.h>

/* error: dereferencing object of size << sizeOfTarget << B out of bounds */

int main() {
    void *mem = malloc(sizeof(char));
    void **err = mem;

    *err = NULL; // invalid deref
    
    free(mem);
    return 0;
}
