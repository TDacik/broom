
// (almost) minimal version derived from original nspr 4.29 plarena.c
// preprocessing done by gcc -E plarena.c
// Original copyright:
/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/*
 * Lifetime-based fast allocation, inspired by much prior art, including
 * "Fast Allocation and Deallocation of Memory Based on Object Lifetimes"
 * David R. Hanson, Software -- Practice and Experience, Vol. 20(1).
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

////////////////////////////////////////////////////////////////////
// NSPR types (for x86_64 linux)

typedef unsigned char PRUint8;
typedef signed char PRInt8;
typedef unsigned short PRUint16;
typedef short PRInt16;
typedef unsigned int PRUint32;
typedef int PRInt32;
typedef long long PRInt64;
typedef unsigned long long PRUint64;
typedef int PRIntn;
typedef unsigned int PRUintn;
typedef double PRFloat64;
typedef size_t PRSize;
typedef PRInt32 PROffset32;
typedef PRInt64 PROffset64;
typedef PRIntn PRBool;
typedef PRUint8 PRPackedBool;
typedef PRUint16 PRUnichar;
typedef long PRWord;
typedef unsigned long PRUword;

////////////////////////////////////////////////////////////////////

typedef struct PLArena PLArena;

struct PLArena {
    PLArena *next;
    PRUword base;
    PRUword limit;
    PRUword avail;
};

typedef struct PLArenaPool PLArenaPool;

struct PLArenaPool {
    PLArena first;
    PLArena *current;
    PRUint32 arenasize;
    PRUword mask;
};

////////////////////////////////////////////////////////////////////

/*
void PL_InitArenaPool(PLArenaPool * pool, const char *name, PRUint32 size, PRUint32 align);
void PL_ArenaFinish(void);
void PL_FreeArenaPool(PLArenaPool * pool);
void PL_FinishArenaPool(PLArenaPool * pool);
void PL_CompactArenaPool(PLArenaPool * pool);
void *PL_ArenaAllocate(PLArenaPool * pool, PRUint32 nb);
void *PL_ArenaGrow(PLArenaPool * pool, void *p, PRUint32 size, PRUint32 incr);
void PL_ArenaRelease(PLArenaPool * pool, char *mark);
void PL_ClearArenaPool(PLArenaPool * pool, PRInt32 pattern);
typedef size_t (*PLMallocSizeFn)(const void *ptr);
size_t PL_SizeOfArenaPoolExcludingPool(const PLArenaPool * pool,
                                       PLMallocSizeFn mallocSizeOf);
*/

/* TODO: use macros */
void *PR_Malloc(PRUint32 size) { return malloc(size); }
void PR_Free(void *ptr) { free(ptr); }

/*
typedef unsigned long prbitmap_t;
PRIntn PR_CeilingLog2(PRUint32 i);
PRIntn PR_FloorLog2(PRUint32 i);
void PR_Assert(const char *s, const char *file, PRIntn ln);
*/

//////////////////////////////////////////////////////////////////
// arena pool initialization
void PL_InitArenaPool(PLArenaPool * pool, const char *name, PRUint32 size, PRUint32 align)
{
    static const PRUint8 pmasks[33] = {
        0,
        0, 1, 3, 3, 7, 7, 7, 7, 15, 15, 15, 15, 15, 15, 15, 15,
        31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31
    };

    if (align == 0) {
        align = sizeof(double);  // default alignment
    }

    if (align < sizeof(pmasks) / sizeof(pmasks[0])) {
        pool->mask = pmasks[align];
    } else {
        abort();
        /* replace with 31 or Error? */
        //pool->mask = (((PRUint32) 1 << (PR_CeilingLog2(align))) - 1);
    }

    pool->first.next = NULL;

    pool->first.base = pool->first.avail = pool->first.limit 
    = (PRUword) (((PRUword) (&pool->first + 1) + (pool)->mask) & ~(pool)->mask);
    pool->current = &pool->first;

    if (size > sizeof(PLArena) + pool->mask) {
        pool->arenasize = size - (sizeof(PLArena) + pool->mask);
    } else {
        pool->arenasize = size;
    }
}

// allocate memory from arena pool (malloc)
void *PL_ArenaAllocate(PLArenaPool * pool, PRUint32 nb)
{
    PLArena *a;
    char *rp;
    PRUint32 nbOld;

    nbOld = nb;
    nb = (PRUword) (((PRUword) (nb) + (pool)->mask) & ~(pool)->mask);
    if (nb < nbOld) {
        return NULL;
    }

    a = pool->current;
    do {
        if (nb <= a->limit - a->avail) {
            pool->current = a;
            rp = (char *) a->avail;
            a->avail += nb;
            return rp;
        }
    } while (NULL != (a = a->next));


    PRUint32 sz = ((pool->arenasize) > (nb) ? (pool->arenasize) : (nb));
    // PR_UINT32_MAX
    if (4294967295U - sz < sizeof *a + pool->mask) {
        a = NULL;
    } else {
        sz += sizeof *a + pool->mask;
        a = (PLArena *) (PR_Malloc((sz)));
    }

    if (NULL != a) {
        a->limit = (PRUword) a + sz;
        a->base = a->avail = (PRUword) (((PRUword) (a + 1) + (pool)->mask) & ~(pool)->mask);
        rp = (char *) a->avail;
        a->avail += nb;
        ((void) 0);


        a->next = pool->current->next;
        pool->current->next = a;
        pool->current = a;
        if (NULL == pool->first.next) {
            pool->first.next = a;
        }
        return (rp);
    }

    return (NULL);
}

// resize memory block allocated in arena pool (realloc)
void *PL_ArenaGrow(PLArenaPool * pool, void *p, PRUint32 size, PRUint32 incr)
{
    void *newp;

    // PR_UINT32_MAX
    if (4294967295U - size < incr) {
        return NULL;
    }

    PLArena *_a = (pool)->current;
    PRUint32 _nb = (((PRUword) ((PRUint32) size + incr) + (pool)->mask) & ~(pool)->mask);
    PRUword _p = _a->avail;
    if (_nb < (PRUint32) size + incr) {
        _p = 0;
    } else if (_nb > (_a->limit - _a->avail)) {
        _p = (PRUword) PL_ArenaAllocate(pool, _nb);
    } else {
        _a->avail += _nb;
    }
    newp = (void *) _p;

    if (newp) {
        memcpy(newp, p, size);
    }
    return newp;
}

// "free" all allocated blocks in all arenas, memset to pattern
void PL_ClearArenaPool(PLArenaPool * pool, PRInt32 pattern)
{
    PLArena *a;

    for (a = pool->first.next; a; a = a->next) {
        a->avail = a->base;
        memset((void *) (a)->avail, (pattern), (a)->limit - (a)->avail);
    }
}

// free all next arenas from given arena
static void FreeArenaList(PLArenaPool * pool, PLArena * head)
{
    PLArena *a = head->next;
    if (!a) {
        return;
    }

    head->next = NULL;

    do {
        PLArena *tmp = a;
        a = a->next;
        PR_Free(tmp);
        (tmp) = NULL;
    } while (a);

    pool->current = head;
}

// RELEASE (after MARK)
void PL_ArenaRelease(PLArenaPool * pool, char *mark)
{
    PLArena *a;
    for (a = &pool->first; a; a = a->next) {
        if (((PRUword) (mark) - (PRUword) (a->base)) <= ((PRUword) (a->avail) - (PRUword) (a->base))) {
            a->avail = (PRUword) (((PRUword) (mark) + (pool)->mask) & ~(pool)->mask);
            FreeArenaList(pool, a);
            return;
        }
    }
}

// free all arenas in pool
void PL_FreeArenaPool(PLArenaPool * pool)
{
    FreeArenaList(pool, &pool->first);
}

// free all arenas in pool
void PL_FinishArenaPool(PLArenaPool * pool)
{
    FreeArenaList(pool, &pool->first);
}

void PL_CompactArenaPool(PLArenaPool * ap)
{
}

void PL_ArenaFinish(void)
{
}

/*
size_t PL_SizeOfArenaPoolExcludingPool(const PLArenaPool * pool, PLMallocSizeFn mallocSizeOf)
{
    size_t size = 0;
    const PLArena *arena = pool->first.next;
    while (arena) {
        size += mallocSizeOf(arena);
        arena = arena->next;
    }
    return size;
}
*/

#ifdef TEST
// TODO: simple test
int main() {
    PLArenaPool pool;
    const unsigned size = 4096*32;
    const unsigned align = 16;

    PL_InitArenaPool(&pool, "name", size, align);

    void * p1 = PL_ArenaAllocate(&pool, 60);
    printf("%p\n", p1);

    void * p2 = PL_ArenaAllocate(&pool, 70);
    printf("%p\n", p2);

#if 1
    void * p3 = PL_ArenaAllocate(&pool, size-10);
    printf("%p\n", p3);
#endif

    PL_FinishArenaPool(&pool);
}
#endif
