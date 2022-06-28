/*
 * Collections-C
 * Copyright (C) 2013-2014 Srđan Panić <srdja.panic@gmail.com>
 *
 * This file is part of Collections-C.
 *
 * Collections-C is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Collections-C is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Collections-C.  If not, see <http://www.gnu.org/licenses/>.
 */

/**
 * @Author: S. Sharma <silentcat>
 * @Date:   2019-03-07T10:32:56-06:00
 * @Email:  silentcat@protonmail.com
 * @Last modified by:   silentcat
 * @Last modified time: 2019-03-09T15:23:25-06:00
 */


#include "cc_common.h"
#include <stdio.h>

#define DEFAULT_CC_RBUF_CAPACITY 10

typedef struct ring_buffer_conf CC_RbufConf;
typedef struct ring_buffer CC_Rbuf;

enum cc_stat  cc_rbuf_new           (CC_Rbuf **rbuf);
// void          cc_rbuf_conf_init     (CC_RbufConf *rconf);
// enum cc_stat  cc_rbuf_conf_new      (CC_RbufConf *rconf, CC_Rbuf **rbuf);
bool          cc_rbuf_is_empty      (CC_Rbuf *rbuf);
void          cc_rbuf_enqueue       (CC_Rbuf *rbuf, uint64_t item);
enum cc_stat  cc_rbuf_dequeue       (CC_Rbuf *rbuf, uint64_t *out);
size_t        cc_rbuf_size          (CC_Rbuf *rbuf);
void          cc_rbuf_destroy       (CC_Rbuf *rbuf);
uint64_t      cc_rbuf_peek          (CC_Rbuf *rbuf, int index);


struct ring_buffer_conf {
    size_t capacity;

//     void *(*mem_alloc)  (size_t size);
//     void *(*mem_calloc) (size_t blocks, size_t size);
//     void  (*mem_free)   (void *block);
};


struct ring_buffer {
    size_t size, capacity;
    size_t head, tail;
    uint64_t    *buf;

//     void *(*mem_alloc)  (size_t size);
//     void *(*mem_calloc) (size_t blocks, size_t size);
//     void  (*mem_free)   (void *block);
};


enum cc_stat cc_rbuf_new(CC_Rbuf **rbuf)
{
    CC_Rbuf *ringbuf = calloc(1, sizeof(CC_Rbuf));

    if (!ringbuf)
        return CC_ERR_ALLOC;

    if (!(ringbuf->buf = calloc(DEFAULT_CC_RBUF_CAPACITY, sizeof(uint64_t)))) {
        free(ringbuf);
        return CC_ERR_ALLOC;
    }

//     ringbuf->mem_alloc   = rconf->mem_alloc;
//     ringbuf->mem_calloc  = rconf->mem_calloc;
//     ringbuf->mem_free    = rconf->mem_free;
    ringbuf->capacity    = DEFAULT_CC_RBUF_CAPACITY;
    ringbuf->size        = 0;
    ringbuf->head        = 0;
    ringbuf->tail        = 0;

    *rbuf = ringbuf;
    return CC_OK;
}


// enum cc_stat cc_rbuf_conf_new(CC_RbufConf *rconf, CC_Rbuf **rbuf)
// {
//     CC_Rbuf *ringbuf = calloc(1, sizeof(CC_Rbuf));
// 
//     if (!ringbuf)
//         return CC_ERR_ALLOC;
// 
//     if (!(ringbuf->buf = calloc(rconf->capacity, sizeof(uint64_t)))) {
//         free(ringbuf);
//         return CC_ERR_ALLOC;
//     }
// 
//     ringbuf->mem_alloc   = rconf->mem_alloc;
//     ringbuf->mem_calloc  = rconf->mem_calloc;
//     ringbuf->mem_free    = rconf->mem_free;
//     ringbuf->capacity    = rconf->capacity;
//     ringbuf->size        = 0;
//     ringbuf->head        = 0;
//     ringbuf->tail        = 0;
// 
//     *rbuf = ringbuf;
//     return CC_OK;
// }


// void cc_rbuf_conf_init(CC_RbufConf *rconf)
// {
//     rconf->capacity = DEFAULT_CC_RBUF_CAPACITY;
//     rconf->mem_alloc = malloc;
//     rconf->mem_calloc = calloc;
//     rconf->mem_free = free;
// }


void cc_rbuf_destroy(CC_Rbuf *rbuf)
{
    free(rbuf->buf);
    free(rbuf);
}


bool cc_rbuf_is_empty(CC_Rbuf *rbuf)
{
    return (rbuf->size == 0);
}


size_t cc_rbuf_size(CC_Rbuf *rbuf)
{
    return rbuf->size;
}


void cc_rbuf_enqueue(CC_Rbuf *rbuf, uint64_t item)
{
    if (rbuf->head == rbuf->tail)
        rbuf->tail = (rbuf->tail + 1) % rbuf->capacity;

    rbuf->buf[rbuf->head] = item;

    rbuf->head = (rbuf->head + 1) % rbuf->capacity;

    if (rbuf->size < rbuf->capacity)
        ++rbuf->size;
}


enum cc_stat cc_rbuf_dequeue(CC_Rbuf *rbuf, uint64_t *out)
{
    if (cc_rbuf_is_empty(rbuf))
        return CC_ERR_OUT_OF_RANGE;

    *out = rbuf->buf[rbuf->tail];

    rbuf->tail = (rbuf->tail + 1) % rbuf->capacity;
    --rbuf->size;
    return CC_OK;
}


uint64_t cc_rbuf_peek(CC_Rbuf *rbuf, int index)
{
    return rbuf->buf[index];
}
