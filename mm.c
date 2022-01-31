/*
 * mm.c
 *
 * Name: [Wei Lin Weng]
 *
 * Dynamic storage allocator solution that has implementations with
 * fast efficient malloc, free, and realloc functions.
 *
 */
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
// #define DEBUG

#ifdef DEBUG
// When debugging is enabled, the underlying functions get called
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
// When debugging is disabled, no code gets generated
#define dbg_printf(...)
#define dbg_assert(...)
#endif // DEBUG

// do not change the following!
#ifdef DRIVER
// create aliases for driver tests
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mm_memset
#define memcpy mm_memcpy
#endif // DRIVER

#define ALIGNMENT 16

// rounds up to the nearest multiple of ALIGNMENT
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

/*
 * Create Struct node_t
 */
 typedef struct __node_t {
     int size;
     struct __node_t *next;
 }node_t;

/*
 * Create Header with size and num
 */
 typedef struct {
     int size;
     int num;
 } header_t;

//Global Variables
int check_mm_init = 0;
(void *)headptr = NULL;


/*
 * mm_init: returns false on error, true on success.
 */
bool mm_init(void)
{
    // IMPLEMENT THIS
    if (check_mm_init == 0){
        //Error occurred
        return false;
    }else{
        check_mm_init = 1;
        return true;
    }
}

/*
 * malloc
 */
void* malloc(size_t size)
{
    // IMPLEMENT THIS
    //char buffer = [1024];
    // Construct Alignment
    const size_t size_mm = align(size);
    struct node_t *node;
    //check if size_mm = 0 or >
    if (size_mm > 0){
    }else{
        return NULL;
    }
}

/*
 * free
 */
void free(void* ptr)
{
    // IMPLEMENT THIS
    header_t *hptr = (header_t *) ptr - 1;
    return;
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
    // IMPLEMENT THIS
    // Check if oldptr equals NUll, if it does, then put size into mm_malloc
    if(oldptr == NULL){
        return mm_malloc(size);
    }
    //Construct a buf node
    struct node_t* buf_ptr = (node_t*) oldptr - 1;
    //Check if the size match
    if(buf_ptr->size >= size){
        return oldptr;
    }else{
        //Create a size of the input size and copy over
        //if size empty, return NULL, else memory copy and free oldptr
        (void *)n_ptr = mm_malloc(size);
        if(n_ptr == NULL){
            return NULL;
        }else{
            mm_memcpy(n_ptr, oldptr, buf_ptr->size);
            mm_free(oldptr);
            return (n_ptr);
        }
    }
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mm_heap_hi() && p >= mm_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    // Write code to check heap invariants here
    // IMPLEMENT THIS
#endif // DEBUG
    return true;
}
