#include <stdlib.h>
#include <stddef.h> /* size_t, offsetof */


// All nodes (=next) must be allocated on (at least) two-byte boundaries
// because the low bit is used as a sentinel to signal end-of-list.
typedef struct link {
  struct link *prev; 
  void *next;
} link;


static link* link_get_next(link* lnk) {
  /* offset from a node pointer to a link structure */
  size_t offset = (size_t) lnk - ((size_t) lnk->prev->next & ~1);
  /* link field for the next node */
  size_t offset_of_next = (size_t) lnk->next & ~1;
  return (link*) (offset_of_next + offset);
}
