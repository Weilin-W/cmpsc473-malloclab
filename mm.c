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

/*
 * Basic constants and macros for manipulating the free list.
 */
#define WSIZE  4 //Word and header/footer size
#define DSIZE  8 //Double word size
#define CHUNKSIZE (1<<12) //Extend heap by this amount

#define MAX(x, y)((x)>(y)?(x):(y))

//Pack a size and allocated bit into a word
#define PACK(size, alloc)((size) | (alloc))
//Read and write a word at address p
#define GET(p) (*(unsigned int* )(p))
#define PUT(p, val) (*(unsigned int* )(p) = (val))
//Read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
//Given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
//Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/*
 * Extends the heap with a new free block
 */
static void *extend_heap(size_t words){

    char *bp;
    size_t size;

    //Allocate an even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words *WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1){
        return(NULL);
    }
    //Initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size, 0));  //Free block header
    PUT(FTRP(bp), PACK(size, 0));  //Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  //New epilogue header

    //Coalesce if the previous block was free
    return coalesce(bp);
 }
 
 /*
  * coalesce pointer function
  */
static void *coalesce(void* bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //Case 1
    if(prev_alloc && next_alloc){
        return bp; //block pointer
    }
    //Case 2
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); //Increase size to next block header size
        PUT(HDRP(bp), PACK(size, 0)); //Free Header
        PUT(FTRP(bp), PACK(size, 0)); //Free Footer
    }
    //Case 3
    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); //Increase size to previous block header size
        PUT(FTRP(bp), PACK(size, 0)); //Free Footer
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); //Free previous header
        bp = PREV_BLKP(bp);
    }
    //Case 4
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); //Increase size to sum of previous block header size and next block footer size
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); //Free previous block header
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); //Free next block footer
        bp = PREV_BLKP(bp); //Set block pointer to previous block pointer
    }
    return (bp); //return block pointer
}
/*
 * Find fit function
 */
static void *find_fit(size_t asize){
    //First fit search
    void *bp;

    for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL; //No fit
}

/*
 * Place function
 */
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
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
    char *bp;

    //Ignore requests if empty
    if(size == 0){
        return NULL;
    }
    //Adjust block size to include overhead and alignment requests
    if(size <= DSIZE){
        asize = 2*DSIZE;
    }else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }
    //Search the free list for a fit
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    //No fit found, Get more memory and place the block
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * free
 */
void free(void* ptr)
{
    // IMPLEMENT THIS
    if(ptr == NULL){
        return;
    }else{
        //free block, write implementation add back to free list.
        //Change allocation....etc
        size_t size = GET_SIZE(HDRP(ptr));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
        coalesce(ptr);
    }
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
    // IMPLEMENT THIS
    // Check if oldptr equals NUll, if it does, then put size into mm_malloc
    /*
    if(oldptr == NULL){
        return malloc(size);
    }
    //Construct a buf node
    struct node_t* buf_ptr = (node_t*) oldptr - 1;
    //Check size equals 0
    if(size == 0){
        free(oldptr);
    }
    //Check if the size match
    if(buf_ptr->size >= size){
        return oldptr;
    }else{
        //Create a size of the input size and copy over
        //if size empty, return NULL, else memory copy and free oldptr
        struct node_t* n_ptr = malloc(size);
        if(n_ptr == NULL){
            return NULL;
        }else{
            memcpy(n_ptr, oldptr, buf_ptr->size);
            free(oldptr);
        }
    }
    return (n_ptr);
    */
    return NULL;
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
