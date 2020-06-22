/*
 * mm.c
 *
 * CMPSC 473
 *
 * Name: Austin Schaefer
 * Email: ads5915@psu.edu
 * PSU ID: 962297172
 *
 * Citation: Computer Systems, A Programmer's Perspective [3rd edition] by Randall E Bryant, David R O'Hallaron
 *
 * 
 *
 *
 * My design isn't fully working as initially intended. I was in the middle of implementing 
 * explicit free list and coalescing, but was unable to finish. I have implemented a heap checker at the bottom,
 * to help me make sure I am allocting right sizes and bits to my headers and footers.
 *
 * mm_init: 
 * From the beginning, I use mm_init to expand the heap by 8 bytes. This serves as a 
 * buffer, so that I can identify my first block of memory. I also use headers and footers for each block, each
 * one is 8 bytes. 
 *
 * Malloc:
 * To ensure the data blocks are aligned, I use an alignment of 16 bytes, and I check this alignment
 * in malloc. My intention was to call find_fit to find space for the requested size, but I didn't get to that.
 * When I get the desired pointer for allocating memory, I call PLACE() to set the allocation bit and size in the
 * headers and footers. 
 *
 * Free and realloc:
 * My free function sets the allocated bits to 0. My realloc function checks the size of the new block, and copies
 * data depending on whether the new block is smaller or bigger than the old block. After transferring data, I would
 * free the old data block.
 *
 *
 *
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"


#define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16
#define HDRSIZE 8
#define FTRSIZE 8


/*	
 *	Global variable for start of explicit free list
 */
char * freelistp;



/* 	
 *	Pack the size and allocated bit together (cited from textbook)	
 */
static inline size_t PACK(size_t size, size_t alloc){ 

	return ((size) | (alloc)); }


/* 	
 *	Place value at specific pointer (cited from textbook)	
 */
static inline void PUT(void *p, size_t val){ 
	
	(*(size_t *)(p) = (val)); }


/* 	
 *	Retrieve the value at pointer p (cited from textbook)	
 */
static inline size_t GET(void *p){ 

	return (*(size_t *)(p)); }


/*	
 *	Read the size/allocated fields from address p (cited from textbook)
 *	Called on header or footers 										
 */
static inline size_t GET_SIZE(void *p){ 
	if (p == NULL){
		return 0;
	}
	return (GET(p) & ~0x1); }


static inline size_t GET_ALLOC(void *p){
	if (p==NULL){return 0;}
	return (GET(p) & 0x1); }


/*
 * 	Returns whether the pointer is in the heap.
 * 	May be useful for debugging.
 */
static inline bool in_heap(const void* p){
    return p <= mem_heap_hi() && p >= mem_heap_lo(); }


/* 	
 *	Return pointer to the block's header (cited from textbook)
 */
static inline char * HDRP(void *bp){
	if (bp == NULL){
		return NULL;
	}
	return ((char *)(bp) - 8); }


/* 	
 *	Return pointer to the block's footer (cited from textbook)	
 */
static inline char * FTRP(void *bp){
	if (bp == NULL){
		return NULL;
	}
	return ((char *)(bp) + GET_SIZE(HDRP(bp)) - 16); }


/*
 *	Return pointer to data of next/previous block, mostly cited from the textbook
 *
 *	Check edge cases, if size=0, pointer is in heap, or pointer is NULL
 */
static inline char * NEXT_BLKP(void *bp){

	char * nextblk = (char *)bp + GET_SIZE( HDRP(bp)) ;
	if (nextblk == NULL){ return NULL; }

	int next_size = GET_SIZE(HDRP(nextblk)) ;

	if (!in_heap(nextblk)){
		return NULL;
	}
	if (next_size == 0){
		return NULL;
	}

	return nextblk; }


static inline char * PREV_BLKP(void *bp){

	char * footerptr = (char *)(bp) - 16;
	if(!in_heap(footerptr)){
		return NULL; }

	int prev_size = GET_SIZE( footerptr ) ;
	if (prev_size == 0){
		return NULL; }

	return ((char *)(bp) - prev_size); }





/* 
 *	Rounds up to the nearest multiple of ALIGNMENT 
 */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

/*
 *	Coalesce has four cases to account for, depending if prev/next blocks are free
 */
static void *coalesce(void *bp)
{
	/* 	Get allocation bit of previous block (cited from textbook)
	 	If pointer is at beginning of heap, set to allocated		*/
	size_t prev_alloc;
	if (in_heap(PREV_BLKP(bp)) ){
		prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); }
	else{ prev_alloc = 1; }

	/* 	Get allocation bit of next block
	 	If pointer is at end of heap, set to allocated		*/
	size_t next_alloc;
	if (in_heap(NEXT_BLKP(bp)) ){
		next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); }
	else{ next_alloc = 1; }

	size_t size = GET_SIZE(HDRP(bp));


	/* If neither are free */
	if (prev_alloc && next_alloc) {
		return bp;	}

	/* If only next is free */
	else if (prev_alloc && !next_alloc) {
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size,0));
	}

	/* If only prev is free */
	else if (!prev_alloc && next_alloc) { 
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	/* If both are free */
	else { 
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
		GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	return bp;
}


/*
 * Initialize: add 8 bytes for the buffer with mem_sbrk, allocate with size 8.
 */
bool mm_init(void)
{
	void * bufptr = mem_sbrk(8);
	
	if (bufptr == (void *) -1){
		return false; }

	PUT(bufptr, PACK(8,1));
	return true;
}


static void *find_fit(size_t asize)
{
	/* 	First-fit search, referenced from textbook. Return data block pointer.
	   	Start search at beginning of heap, go through whole heap.				*/
 	void *bp;

 	for (bp = mem_heap_lo() + 8; in_heap(bp) && GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {

 			return bp;
 		}
 	}
 	// If no space, return NULL
 	return NULL;
}


/*	
 *	Placing data in memory, referenced from the textbook. 
 *	Set data and allocate memory. Failed attempt to split memory.	
 */
static void place(void *bp, size_t datasize)
{
//	size_t blocksize = GET_SIZE(HDRP(bp));
	// size_t smallsize = blocksize - datasize;
	// void *newblkptr;

 // 	if (smallsize > 32) {
 // 		PUT(HDRP(bp), PACK(datasize, 1));
 // 		PUT(FTRP(bp), PACK(datasize, 1));
	// 	newblkptr = NEXT_BLKP(bp);
	// 	PUT(HDRP(newblkptr), PACK(smallsize, 0));
	// 	PUT(FTRP(newblkptr), PACK(smallsize, 0));
	// }
	// else {
 		PUT(HDRP(bp), PACK(datasize, 1));
 		PUT(FTRP(bp), PACK(datasize, 1));
//	}
}


// Failed attempt at explicit free list
/*
static void placefree(void *bp){
	// If freelistp is null, initialize to pointer
	if (freelistp == NULL){
		freelistp = bp;
		(*(void **)(freelistp + HDRSIZE)) = NULL;
		(*(void **)(freelistp)) = NULL;
	}

	else{
		freelistp
	}
} */



/*
 * 	malloc: If no available memory, expand the heap. Place size and mark it as allocated
 */
void* malloc(size_t size)
{
	/* If user requests for 0 or less space, return NULL. */
    if (size <=0){
    	return NULL;
    }

	/* Adjusted block size */
    size_t asize; 
	asize = align(size + 16);

	/* Pointer to data block, initialized because find_fit isn't working  */
	char *bp = NULL;


//	bp = find_fit(asize);

	if (bp == NULL){
		bp = mem_sbrk(asize);
		bp = bp + 8;
	}

	place(bp,asize);

	mm_checkheap(__LINE__);

	return bp;
	 
} 




/*
 * 	free: allocated bit = 0 means block is freed
 */
void free(void* ptr)
{
    /* Set allocated bit to 0, cited from textbook */

    size_t size = GET_SIZE(HDRP(ptr));

	PUT(HDRP(ptr), PACK(size, 0));
	PUT(FTRP(ptr), PACK(size, 0));
//	coalesce(ptr);
  
}


/*
 * 	Reallocate old data to a new block, depending on the size of the new block.
 * 	Return the pointer to the new memory location
 */
void* realloc(void* oldptr, size_t size)
{	
	/*  If there is no data to realloc, malloc to accommodate for the new size */
	void *newptr;
	if (oldptr == NULL){
		newptr = malloc(size);
		return newptr;
	}

	/* If the new size is 0, there is nowhere to put the data. */
	if (size == 0){
		free(oldptr);
		return NULL;
	}
	newptr = malloc(size);
	size_t oldsize = GET_SIZE(HDRP(oldptr)) - HDRSIZE - FTRSIZE;
	size_t newsize = GET_SIZE(HDRP(newptr)) - HDRSIZE - FTRSIZE;


	/* 	If new block has more space, copy size of old memory. 
		Else, copy size of the new memory 						*/

	if (newsize>oldsize){
		mem_memcpy(newptr, oldptr, oldsize);
	}
	else{
		mem_memcpy(newptr, oldptr, size);
	}

	//	mm_checkheap(__LINE__);
	free(oldptr);

    return newptr;
}


/*
 * 	calloc
 * 	This function is not tested by mdriver, and has been implemented for you.
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
 * 	Returns whether the pointer is aligned, making sure data blocks line up
 * 
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * 	Heapchecker checks if the headers and footers are next to each other, and that the size and allocated bit match
 * 	Checks from the beginning of the heap, until 1024 bytes.
 * 	Useful for checking the sizes of the test blocks too.
 * 	If there are any errors, it will print information from the header and footer of the block.
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    void *bp;
    int inc = 0;
    size_t hdr_after_ftr = 0;
    size_t prevftr = 0;


 	for (bp = mem_heap_lo() + 16; in_heap(bp) && bp<mem_heap_lo()+1024; bp = NEXT_BLKP(bp)){
 		inc ++;
 		bool checksize = GET_SIZE(HDRP(bp)) == GET_SIZE(FTRP(bp));
 		bool checkalloc = GET_ALLOC(HDRP(bp)) == GET_ALLOC(FTRP(bp));

 		
 		/* For the first block, check if the buffer comes before the header */
 		if (inc == 1){
 			hdr_after_ftr = GET_SIZE(bp - 16);
 			if (hdr_after_ftr == 8){
 				 dbg_printf("Size of buffer: %lu\n",hdr_after_ftr);
 			}
 		}
 		else{
 			hdr_after_ftr = GET_SIZE(FTRP(PREV_BLKP(bp)));
 			// if(hdr_after_ftr == prevftr){
 			// dbg_printf("MATCH: Footer size of previous block: %lu\nGo back 16 bytes from current header: %lu\n", prevftr, hdr_after_ftr);
 			// dbg_printf("Block number: %d\n", inc);
 			// }
 		 	if(hdr_after_ftr == prevftr){
 		 	dbg_printf("MISMATCH: Footer size of previous block: %lu\nGo back 16 bytes from current header: %lu\n", prevftr, hdr_after_ftr);
 		 	dbg_printf("Block number: %d\n", inc);
 		 	}
 		}
 		
 		
 		if (checksize || checkalloc){
 			dbg_printf("Block Number: %d\n", inc);
 			dbg_printf("Header size: %lu , Footer size: %lu\n", GET_SIZE(HDRP(bp)), GET_SIZE(FTRP(bp)));
 			dbg_printf("Alloc header: %lu , Alloc footer: %lu\n\n", GET_ALLOC(HDRP(bp)), GET_ALLOC(FTRP(bp)));
 		}

		prevftr = GET_SIZE(FTRP(bp));


 	}
    /* IMPLEMENT THIS */
#endif /* DEBUG */
    return true;
}
