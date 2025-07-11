// frama-c -wp -rte -wp-timeout 180 -wp-prover alt-ergo,cvc4,z3 -wp-prop="-@lemma" memb.c -then -report -report-no-proven -report-print-properties 

/*
 * Copyright (c) 2004, Swedish Institute of Computer Science.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the Institute nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file is part of the Contiki operating system.
 *
 * Author: Adam Dunkels <adam@sics.se>
 *
 */

/**
 * \addtogroup memb
 * @{
 */

 /**
 * \file
 * Memory block allocation routines.
 * \author Adam Dunkels <adam@sics.se>
 */
#include <string.h>

struct memb {
  unsigned short size;
  unsigned short num;
  char *count;
  void *mem;
};

#include "count.acsl"


/*@
  predicate valid_memb(struct memb *m) =
    \valid(m)
    && \valid(m->count + (0 .. (m->num - 1)))
    && \valid((char*) m->mem + (0 .. (m->size * m->num - 1)))
    && m->size > 0
    && m->size * m->num <= INT_MAX
    && \separated(m->count + (0 .. (m->num - 1)), 
                    (char*) m->mem + (0 .. m->size * m->num - 1));
*/

/*@ lemma mult_simplification:
      \forall integer a, b; a >= 0 ==> b > 0 ==> (a * b) / b == a;
*/

/*@ // Converting from pointer to index and backwards.
  logic integer _memb_index(struct memb *m, void *ptr) =
    (ptr - m->mem) / m->size;
  logic void * _memb_ptr(struct memb *m, integer index) =
    (void*) ((char*) m->mem + index * m->size);
  // Counting free elements.
  logic integer _memb_numfree(struct memb *m) = count(0, m->count, 0, m->num);
  // Helper predicates. For readability.
  predicate _memb_has(struct memb *m, void *ptr) =
    \exists integer i; 0 <= i < m->num && ptr == _memb_ptr(m, i);
  predicate _memb_allocated(struct memb *m, void *ptr) =
    _memb_has(m, ptr) && m->count[_memb_index(m, ptr)] != 0;
  predicate _memb_empty(struct memb *m) =
    \forall integer i; 0 <= i < m->num ==> m->count[i] == 0;
  predicate _memb_full(struct memb *m) =
    \forall integer i; 0 <= i < m->num ==> m->count[i] != 0;
*/





/*@
  requires valid_memb(m);
  ensures valid_memb(m);
  ensures _memb_empty(m);
  assigns m->count[0 .. (m->num - 1)];
  assigns *((char*) m->mem + (0 .. (m->size * m->num - 1)));
*/
void
memb_init(struct memb *m)
{
  /*@ loop invariant 0 <= i <= m->num;
      loop invariant \forall integer k; 0<=k<i ==> m->count[k] == 0;
      loop assigns i, m->count[0..m->num-1];
      loop variant m->num - i;
  */
  for(size_t i = 0; i < m->num; i++) m->count[i] = 0;

  /*@ loop invariant 0 <= i <= m->num * m->size;
      loop invariant \forall integer k; 0<=k<i ==> ((char*)m->mem)[k] == 0;
      loop assigns i, ((char*)m->mem)[0..m->num*m->size-1];
      loop variant m->num*m->size - i;
  */
  for(size_t i = 0; i < m->num * m->size; i++) ((char*)m->mem)[i] = 0;
}
/*---------------------------------------------------------------------------*/
/*@
  requires valid_memb(m);
  ensures valid_memb(m);
  assigns m->count[0 .. (m->num - 1)];
  behavior free_found:
    assumes \exists integer i; 0 <= i < m->num && m->count[i] == 0;
    ensures \exists integer i;
      0 <= i < m->num &&
      \old(m->count[i]) == 0 &&
      m->count[i] == 1 &&
      \result == (char*) m->mem + (i * m->size) &&
      \forall integer j; (0 <= j < i || i < j < m->num) ==> m->count[j] == \old(m->count[j]);
    ensures \valid((char*) \result + (0 .. (m->size - 1)));
    ensures _memb_numfree(m) == \old(_memb_numfree(m)) - 1;
    ensures _memb_allocated(m, \result);
  behavior full:
    assumes _memb_full(m);
    ensures \forall integer i; 0 <= i < m->num ==> m->count[i] == \old(m->count[i]);
    ensures _memb_numfree(m) == \old(_memb_numfree(m));
    ensures \result == NULL;
  complete behaviors;
  disjoint behaviors;
*/
void *
memb_alloc(struct memb *m)
{
  int i;

  /*@
    loop invariant 0 <= i <= m->num;
    loop invariant \forall int j; 0 <= j < i ==> m->count[j] != 0;
    loop assigns i;
    loop variant m->num - i;
  */
  for(i = 0; i < m->num; ++i) {
    if(m->count[i] == 0) {
      /*@ assert whole_cut_before: count(0,m->count,0,m->num) == 
            count(0,m->count,0,i) + count(0,m->count,i,m->num); */
      /*@ assert part_cut_before: count(0,m->count,i,m->num) == 
            count(0,m->count,i,i+1) + count(0,m->count,i+1,m->num); */

      /* If this block was unused, we increase the reference count to
	 indicate that it now is used and return a pointer to the
	 memory block. */
    Before:
      ++(m->count[i]);
      /*@ assert same_elems{Before,Here}(m->count,0,i); */
      /*@ assert same_elems{Before,Here}(m->count,i+1,m->num); */
      /*@ assert whole_cut: count(0,m->count,0,m->num) == 
            count(0,m->count,0,i) + count(0,m->count,i,m->num); */
      /*@ assert part_cut: count(0,m->count,i,m->num) == 
            count(0,m->count,i,i+1) + count(0,m->count,i+1,m->num); */
      /*@ assert 0 <= i * m->size; */ 
      /*@ assert i * m->size <= (m->num - 1) * m->size; */
      return (void *)((char *)m->mem + (i * m->size));
    }
  }
  /* No free block was found, so we return NULL to indicate failure to
     allocate block. */
  return NULL;
}



/*---------------------------------------------------------------------------*/
/*@
  requires valid_memb(m);
  ensures valid_memb(m);
  assigns m->count[_memb_index(m, ptr)];
  behavior alloc_found:
    assumes _memb_has(m, ptr) && _memb_allocated(m, ptr);
    ensures !_memb_allocated(m, ptr);
    ensures _memb_numfree(m) == \old(_memb_numfree(m)) + 1;
    ensures \result == 0;
  behavior already_free:
    assumes _memb_has(m, ptr) && !_memb_allocated(m, ptr);
    ensures !_memb_allocated(m, ptr);
    ensures _memb_numfree(m) == \old(_memb_numfree(m));
    ensures \result == 0;
  behavior elem_notfound:
    assumes !_memb_has(m, ptr);
    ensures m->count[_memb_index(m, ptr)] == \old(m->count[_memb_index(m, ptr)]);
    ensures _memb_numfree(m) == \old(_memb_numfree(m));
    ensures \result == -1;
  complete behaviors;
  disjoint behaviors;
*/
char memb_free(struct memb *m, void *ptr)
{
  int i;
  char *ptr2;
  /* Walk through the list of blocks and try to find the block to
     which the pointer "ptr" points to. */
  ptr2 = (char *)m->mem;
  /*@
    loop invariant 0 <= i <= m->num;
    loop invariant valid_memb(m);
    //loop invariant i < m->num ==> (m->count[i] == 0 || m->count[i] == 1);
    loop invariant ptr2 == _memb_ptr(m, i);
    loop invariant i == _memb_index(m, _memb_ptr(m, i));
    loop invariant \forall int j; 0 <= j < i ==> (char*) ptr != (char*) m->mem + (j * m->size);
    loop assigns i, ptr2;
    loop variant m->num - i;
  */
  for(i = 0; i < m->num; ++i) {
    /*@ assert whole_cut_before: count(0, m->count, 0, m->num) == 
            count(0, m->count, 0, i) + count(0, m->count, i, m->num); */
    /*@ assert part_cut_before: count(0,m->count,i,m->num) == 
            count(0, m->count, i, i+1) + count(0 ,m->count, i+1, m->num); */
    if(ptr2 == (char *)ptr) {
      /* We've found to block to which "ptr" points so we decrease the
	 reference count and return the new value of it. */
   Before:
      m->count[i] = 0;
      /*@ assert same_elems{Before,Here}(m->count,0,i); */
      /*@ assert same_elems{Before,Here}(m->count,i+1,m->num); */
      /*@ assert whole_cut: count(0,m->count,0,m->num) == 
            count(0,m->count,0,i) + count(0,m->count,i,m->num); */
      /*@ assert part_cut: count(0,m->count,i,m->num) == 
            count(0,m->count,i,i+1) + count(0,m->count,i+1,m->num); */
      /*@ assert \at(m->count[i], Before) !=0 ==> 
           _memb_numfree(m) == \at(_memb_numfree(m), Pre) + 1; */
      return m->count[i];
    }
    ptr2 += m->size;
  }
  return -1;
}
/*---------------------------------------------------------------------------*/
/*@
  requires valid_memb(m);
  ensures \result <==> (m->mem <= ptr && (char*) ptr < (char*) m->mem + (m->num * m->size));
  assigns \nothing;
*/
int
memb_inmemb(struct memb *m, void *ptr)
{
  return (char *)ptr >= (char *)m->mem &&
    (char *)ptr < (char *)m->mem + (m->num * m->size);
}
/*---------------------------------------------------------------------------*/
/*@
  requires valid_memb(m);
  ensures \result == _memb_numfree(m);
  assigns \nothing;
*/
int
memb_numfree(struct memb *m)
{
  int i;
  int num_free = 0;

  /*@
    loop invariant 0 <= i <= m->num;
    loop invariant num_free <= i;
    loop invariant num_free == count(0, m->count, 0, i);
    loop assigns i, num_free;
    loop variant m->num - i;
  */
  for(i = 0; i < m->num; ++i) {
    if(m->count[i] == 0) {
      ++num_free;
    }
  }

  return num_free;
}
/** @} */
