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
 *Global Variables
 */
static char *heap_listp; //Ptr to first block

/*
 * Functions Declare
 */
static void *coalesce(void* ptr);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *ptr, size_t asize);

/*
 * Basic constants and static function for manipulating the free list.
 */
#define WSIZE  8 //Word and header/footer size
#define DSIZE  16 //Double word size
#define CHUNKSIZE (1<<12) //Extend heap by this amount

int MAX(int x, int y){
    if(x > y){
        return x;
    }else{
        return y;
    }
}

//Pack a size and allocated bit into a word
static uint64_t PACK(size_t size, bool alloc){
    return ((size) | (alloc));
}
//Read and write a word at address p
static uint64_t GET(void* p){
    return (*(unsigned int* )(p));
}
static void PUT(void* p, uint64_t val){
    (*(unsigned int* )(p) = (val));
}
//Read the size and allocated fields from address p
static uint64_t GET_SIZE(void* p){
    return (GET(p) & !(DSIZE - 1));
}
static bool GET_ALLOC(void* p){
    return (GET(p) & 0x1);
}
//Given block ptr ptr, compute address of its header and footer
static char* HDRP(void* ptr){
    return ((char *)(ptr)-WSIZE);
}
static char* FTRP(void* ptr){
    return ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE);
}
//Given block ptr ptr, compute address of next and previous blocks
static char* NEXT_BLKP(void* ptr){
    return ((char *)(ptr) + GET_SIZE(((char *)(ptr) - WSIZE)));
}
static char* PREV_BLKP(void* ptr){
    return ((char *)(ptr) - GET_SIZE(((char *)(ptr) - DSIZE)));
}

/*
 * Extends the heap with a new free block
 */
static void *extend_heap(size_t words){

    char *ptr;
    size_t size;
    
    //Allocate an even number of words to maintain alignment
    //size = (words % 2) ? (words + 1) * WSIZE : words *WSIZE;
    if(words % 2 == 0){
        size = (words + 1) * WSIZE;
    }else{
        size = words * WSIZE;
    }
    if((long)(ptr = mem_sbrk(size)) == -1){
        return(NULL);
    }
    //Initialize free block header/footer and the epilogue header
    PUT(HDRP(ptr), PACK(size, 0));  //Free block header
    PUT(FTRP(ptr), PACK(size, 0));  //Free block footer
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));  //New epilogue header

    //Coalesce if the previous block was free
    return coalesce(ptr);
 }
 
 /*
  * coalesce pointer function
  */
static void *coalesce(void* ptr){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    //Case 1
    if(prev_alloc && next_alloc){
        return ptr; //block pointer
    }
    //Case 2
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr))); //Increase size to next block header size
        PUT(HDRP(ptr), PACK(size, 0)); //Free Header
        PUT(FTRP(ptr), PACK(size, 0)); //Free Footer
    }
    //Case 3
    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))); //Increase size to previous block header size
        PUT(FTRP(ptr), PACK(size, 0)); //Free Footer
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0)); //Free previous header
        ptr = PREV_BLKP(ptr);
    }
    //Case 4
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(FTRP(NEXT_BLKP(ptr))); //Increase size to sum of previous block header size and next block footer size
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0)); //Free previous block header
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0)); //Free next block footer
        ptr = PREV_BLKP(ptr); //Set block pointer to previous block pointer
    }
    return (ptr); //return block pointer
}
/*
 * Find fit function
 */
static void *find_fit(size_t asize){
    //First fit search
    void *ptr;

    for(ptr = heap_listp; GET_SIZE(HDRP(ptr)) > 0; ptr = NEXT_BLKP(ptr)){
        if(!GET_ALLOC(HDRP(ptr)) && (asize <= GET_SIZE(HDRP(ptr)))){
            return ptr;
        }
    }
    return NULL; //No fit
}

/*
 * Place function
 */
static void place(void *ptr, size_t asize){
    size_t csize = GET_SIZE(HDRP(ptr));

    if((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        ptr = NEXT_BLKP(ptr);
        PUT(HDRP(ptr), PACK(csize - asize, 0));
        PUT(FTRP(ptr), PACK(csize - asize, 0));
    }else{
        PUT(HDRP(ptr), PACK(csize, 1));
        PUT(FTRP(ptr), PACK(csize, 1));
    }
}


/*
 * mm_init: returns false on error, true on success.
 */
bool mm_init(void)
{
    // IMPLEMENT THIS
    //Create the initial empty heap
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1){
        return false;
    }
    PUT(heap_listp, 0); //Alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); //Prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); //Prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); //Epilogue header
    heap_listp += (2*WSIZE);

    //Extend the empty heap with a free block of CHUNKSIZE bytes
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return false;
    }
    return true;
}

/*
 * malloc
 */
void* malloc(size_t size)
{
    // IMPLEMENT THIS
    // Find space, free size of heap, multiple heap block, allocate, find free block, use, else create new block
    size_t asize; // Adjusted block size
    size_t extendsize; //Amount to extend heap if no fit
    char *ptr;

    //Ignore requests if empty
    if(size == 0){
        return NULL;
    }
    //Adjust block size to include overhead and alignment requests
    if(size <= DSIZE){
        asize = 2*DSIZE;
    }else{
        asize = align(size);
    }
    //Search the free list for a fit
    if((ptr = find_fit(asize)) != NULL){
        place(ptr, asize);
        return ptr;
    }

    //No fit found, Get more memory and place the block
    extendsize = MAX(asize, CHUNKSIZE);
    if((ptr = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(ptr, asize);
    return ptr;
}

/*
 * free
 */
void free(void* ptr)
{
    // IMPLEMENT THIS
    if(ptr == NULL){
        return;
    }
    //free block, write implementation add back to free list.
    //Change allocation....etc
    size_t size = GET_SIZE(HDRP(ptr));
    if(heap_listp == NULL){
        mm_init();
    }
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
    
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
    // IMPLEMENT THIS
    size_t oldsize;
    void* newptr;
    // Check if oldptr equals NUll, if it does, then put size into mm_malloc
    if(oldptr == NULL){
        return malloc(size);
    }
    //Check size equals 0
    if(size == 0){
        free(oldptr);
        return NULL;
    }
    newptr = malloc(size);
    //Create a size of the input size and copy over
    if(newptr == NULL){
        return NULL;
    }else{
        //Get oldptr size, copy over oldptr size to newly created size ptr, free the oldptr
        oldsize = GET_SIZE(HDRP(oldptr));
        if(oldsize > size){
            oldsize = size;
        }
        memcpy(newptr, oldptr, oldsize);
        free(oldptr);
    }
    return (newptr);
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
