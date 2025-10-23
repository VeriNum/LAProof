#ifndef ALLOC_H
#define ALLOC_H

//ldoc on
/**
 * # `alloc.h`: Memory allocation
 * 
 * The C `malloc`/`calloc` may return `NULL` to indicate out-of-memory.
 * We would rather have functions that, if they return at all, guarantee
 * to have allocated what's requested.
 *
 * Also, convenient to have specific-typed versions of `calloc` for allocating arrays.
 */

void *surely_malloc(size_t); // Guarantees to allocate, if it returns at all
double *double_calloc(int n);  // Allocate and zero an array of n doubles
int *int_calloc(int n);     // Allocate and zero an array of n ints

void double_clear(double *p, int n);    // Set an array of n doubles to zeros

//ldoc off
#endif /* ALLOC_H */
