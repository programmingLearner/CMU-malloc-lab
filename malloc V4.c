/******************************************************************************************************
 * 1500017799 ZhaoTianyang                                                                            *
 * Malloc-lab                                                                                         *
 * Version 1.0                                                                                        *
 *                                                                                                    *
 * Basic Information:                                                                                 *
 * 1. Inplementation with binary search tree (explicit list)                                          *
 * 2. Alignment by 8 bytes (2 words), each block: no shorter than 4 words                             *
 * 3. Inner displacement protocal of a free block:                                                    *
 *	head (1 word) + left-child-offset (1 word) + right-child-offset (1 word) + ... + foot (1 word)*
 *	head/foot: the length of the block in bytes; last bit: alloc; second last bit: prev-alloc     *
 *	the reason why we use offset instead of addr: otherwise it may take 2 words for a 64-bit addr *
 * 4. The logical structure of the explicit free list is organized into a binary search tree,         *
 *	in which the left child tree represents those blocks                                          *
 *	whose length is shorter than or equal to the length of current block                          *
 * 5. Prelogue block and epilogue block is included similar to the version described in the text book *
 ******************************************************************************************************/

/******************************************************************************************************
 *                                           "do not change"                                          *
 ******************************************************************************************************/
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

/******************************************************************************************************
 *                                         Global Variebles                                           *
 ******************************************************************************************************/
static void* heap_listp;	//CAUTION: 8 bytes in 64-bit system
static void* free_listp = NULL;	//the root of the BST of free lists

/******************************************************************************************************
 *                                               Macros                                               *
 ******************************************************************************************************/
//CAUTION: unsigned instead of int should be used

#define WSIZE	4	//word
#define DSIZE	8	//double word
#define QSIZE	16	//four words (minimum block size)

#define CHUNKSIZE	(1 << 9)	//extend heap by this amount (bytes), to be modified

#define MAX(x, y)	((x) > (y)? (x) : (y))

#define PACK(size, alloc, prev_alloc)	((unsigned int)((size) | (alloc) | (prev_alloc << 1)))	
					//prev_alloc: if the previous block is allocated

//address p
#define GET(p)	(*(unsigned int *)(p))	
#define PUT(p, val)	(*(unsigned int *)(p) = (unsigned int)(val))
	//CAUTION: int type for 4 bytes; long type for 8 bytes, used for addr calcs,
	//but long type should never be used to be put or got in the protocal defined here 
	//(offset instead of addr)

#define GET_SIZE(p)	(GET(p) & ~0x7)
#define GET_ALLOC(p)	(GET(p) & 0x1)
#define GET_PREV_ALLOC(p)	((GET(p) & 0x2) >> 1)

//Given block ptr bp, compute address of its header and footer
#define HDRP(bp)	((char *)(bp) - WSIZE)
#define FTRP(bp)	((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp)	((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)	((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
	//CAUTION: should not be used when GET_PREV_ALLOC is true

//for bst management;
	//CAUTION: if the node has no child, its child-OFFSET instead of child-ADDRESS is 0
#define GET_LCO(bp)	(GET(bp))	//left-child offset
#define GET_RCO(bp)	(GET((char *)(bp) + WSIZE))

#define PUT_LCO(bp, offset)	PUT((bp), offset)	//set left child offset
#define PUT_RCO(bp, offset)	PUT(((char *)(bp) + WSIZE), offset)

#define SET_PREV_ALLOC1(bp, val)	(PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)), val)))
#define SET_PREV_ALLOC2(bp, val)	(PUT(FTRP(bp), PACK(GET_SIZE(FTRP(bp)), GET_ALLOC(FTRP(bp)), val)))
#define SET_PREV_ALLOC(bp, val)		{SET_PREV_ALLOC1(bp, val); SET_PREV_ALLOC2(bp, val);}
	//set prev-alloc bit without altering other infomation
	//CAUTION: if bp points to a free block, SET_PREV_ALLOC should be called; otherwise, ALLOC1 should be called

#define O2P(offset)	((void *)(heap_listp + offset))	//compute address, given offset
#define P2O(addr)	((unsigned int)(addr - heap_listp))	//compute offset, given address
	//CAUTION: the reason why we do not provide a macro to get the address of the child of a given node
		//is to avoid confusing errors that tries to manipulate a 0 offset

/*NEW VERSION: Optimize the case when large number of malloc reqs of same size happens, otherwise the BST will
	become a list and have terrible throughput. Our make-do solution is to use address comparison
	to be a substitude of size comparison. Implementation with hash techneque. Better solution should 
	maintain a list when same size.*/
#define HASH(p)	((unsigned int)((((unsigned long)(p)) >> 3) & 1023))

/******************************************************************************************************
 *                                        Function prototypes                                         *
 ******************************************************************************************************/
int mm_init(void);
static void *extend_heap(size_t words);
void free(void *bp);
static void *coalesce(void *bp);
void bst_add(void *bp);
void bst_delete(void *bp);
void exit_from_error();
void *malloc(size_t size);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
void *calloc(size_t nmemb, size_t size);
void *realloc(void *oldptr, size_t size);
static int in_heap(const void *p);
static int aligned(const void *p);
void mm_checkheap(int lineno);
inline unsigned int hash(void* p);

/******************************************************************************************************
 *                                             Functions                                              *
 ******************************************************************************************************/
/*********************************************************
 *    Initialize: return -1 on error, 0 on success.      *
 *********************************************************/
int mm_init(void){	//checked
	//printf("init called\n");
	free_listp = NULL;

	//create the initial empty heap
	if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return -1;
	PUT(heap_listp, 0);	//alignment padding
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1, 1));	//prologue header
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1, 1));	//prologue footer
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1, 1));	//epilogue header
	heap_listp += (2 * WSIZE);

	//extend the empty heap with a free block of CHUNKSIZE bytes
	if(extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return -1;

	return 0;
}

/*********************************************************
 *                     extend heap                       *
 *********************************************************/
static void *extend_heap(size_t words){	//checked
	//printf("extend called, words = %u\n", (unsigned)words);
	//mm_checkheap(168);
	char *bp;
	size_t size;

	//allocate an even number of words to maintain alignment
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if((long)(bp = mem_sbrk(size)) == -1)
		return NULL;
	//initialize free block header/footer and the epilogue header
	int prev_alloc = GET_PREV_ALLOC(HDRP(bp));
	//printf("bp = %lu\n", (unsigned long)bp);
	PUT(HDRP(bp), PACK(size, 0, prev_alloc));	//free block header
	PUT(FTRP(bp), PACK(size, 0, prev_alloc));	//free block footer
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1, 0));	//new epilogue header

	//mm_checkheap(183);
	//coalesce if the previous block was free
	return coalesce(bp);
}

/*********************************************************
 *                       malloc                          *
 *********************************************************/
void *malloc(size_t size){	//checked
	//printf("malloc called, size = %u\n", (unsigned)size);
	//mm_checkheap(200);

	size_t asize;	//adjusted block size
	size_t extendsize;	//amount to extend heap if not fit
	char* bp;
	
	if(heap_listp == NULL)
        	mm_init();

	//ignore spurious requests
	if(size == 0)
		return NULL;

	//adjust block size to include overhead and alignment requires
	if(size <= 3 * WSIZE)
		asize = QSIZE;
	else
		asize = DSIZE * ((size + (WSIZE) + (DSIZE - 1)) / DSIZE);

	//search the free list for a fit
	if((bp = find_fit(asize)) != NULL){
		place(bp, asize);
		return bp;
	}
	
	//no fit found. get more memory and place the block
	extendsize = MAX(asize, CHUNKSIZE);
	if((bp = extend_heap(extendsize / WSIZE)) == NULL)
		return NULL;
	place(bp, asize);

	return bp;
}

/*********************************************************
 *                        free                           *
 *********************************************************/
void free(void *bp){
	//printf("free called, bp = %lu\n", (unsigned long)bp);
	if (bp == NULL) 
        	return;

   	size_t size = GET_SIZE(HDRP(bp));
	int prev_alloc = GET_PREV_ALLOC(HDRP(bp));

	if(heap_listp == 0){
        	mm_init();
   	}

	PUT(HDRP(bp), PACK(size, 0, prev_alloc));
	PUT(FTRP(bp), PACK(size, 0, prev_alloc));
	coalesce(bp);	
}

/*********************************************************
 *                      coalesce                         *
 * the BST should be maintained by this funciton         *
 *********************************************************/
static void *coalesce(void *bp){	//checked
	//printf("coalesce called, bp = %lu\n", (unsigned long)bp);
	//mm_checkheap(253);
	size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	void *next_blkp_after = NEXT_BLKP(bp); //point to the next block after coalesce		
	
	//case 1
	if(prev_alloc && next_alloc){	
		PUT(HDRP(bp), PACK(size, 0, 1));
		PUT(FTRP(bp), PACK(size, 0, 1));
		bst_add(bp);	//add to free-list-BST
	}
	
	//case 2
	else if(prev_alloc && !next_alloc){
		bst_delete(NEXT_BLKP(bp));
		next_blkp_after = NEXT_BLKP(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0, 1));
		PUT(FTRP(bp), PACK(size, 0, 1));
		bst_add(bp);
	}

	//case 3
	else if(!prev_alloc && next_alloc){
		bst_delete(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0, 1));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, 1));
		bp = PREV_BLKP(bp);
		bst_add(bp);
	}

	//case 4
	else{
		bst_delete(PREV_BLKP(bp));
		bst_delete(NEXT_BLKP(bp));		
		next_blkp_after = NEXT_BLKP(NEXT_BLKP(bp));		
		size += GET_SIZE(HDRP(PREV_BLKP(bp)))
			+ GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, 1));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0, 1));
		bp = PREV_BLKP(bp);
		bst_add(bp);
	}
	
	SET_PREV_ALLOC1(next_blkp_after, 0);	//maintain the prev-alloc bit
	//mm_checkheap(300);
	return bp;
}

/*********************************************************
 *                     bst_add                           *
 * add new free block to the BST of free blocks          *  
 *********************************************************/
void bst_add(void *bp){	//checked
	//printf("bst_add called: bp = %lu\n", (unsigned long)bp);
	//mm_checkheap(310);

	//case1: empty tree now
	if(free_listp == NULL){
		free_listp = bp;
		PUT_LCO(bp, 0);
		PUT_RCO(bp, 0);
		return;
	}
	
	//case2: not empty
	size_t size = GET_SIZE(HDRP(bp));
	void *root = free_listp;
	int lr_flag = 0;	//0 for left-child, 1 for right-child

	//search the parent of bp
	while(1){
		size_t root_size = GET_SIZE(HDRP(root));
		if((size < root_size) || ((size == root_size) && (HASH(bp) <= HASH(root)))){	
				// <=: true, <: false! consider deleting
		//if(size <= root_size){
			if(GET_LCO(root) == 0)
				break;
			root = heap_listp + GET_LCO(root);
			continue;
		}
		else{
			if(GET_RCO(root) == 0){
				lr_flag = 1;
				break;
			}
			root = heap_listp + GET_RCO(root);
			continue;
		}
	}
	
	//found: now root point to bp's parent
	if(lr_flag)	//bp is the right child of the root
		PUT_RCO(root, ((unsigned int)(bp - heap_listp)));
	else	//left
		PUT_LCO(root, ((unsigned int)(bp - heap_listp)));

	//set bp's lco & rco
	PUT_LCO(bp, 0);
	PUT_RCO(bp, 0);

	//mm_checkheap(354);
	return;
}

/*********************************************************
 *                     bst_delete                        *
 * delete free block from the BST of free blocks         *  
 *********************************************************/
void bst_delete(void *bp){	//checked
	//printf("bst_delete called: delete %lu\n", (unsigned long)bp);
	//mm_checkheap(364);

	if(bp == NULL)
		return;

	//case1: empty tree now
	if(free_listp == NULL){
		printf("ERROR: try to delete a node from an empty BST! %lx\n", (unsigned long)bp);
		exit_from_error();
	}
	
	//case2: not empty
	size_t size = GET_SIZE(HDRP(bp));
	void *root = free_listp;

	//search the parent of bp
	int root_flag = 0;	//1: if bp is the root of the BST
	int lr_flag = 0;	//0 for left-child, 1 for right-child

	if(bp == root)	//special case: bp is the root
		root_flag = 1;
	else{	
		while(1){
			size_t root_size = GET_SIZE(HDRP(root));
			if((size < root_size) || ((size == root_size) && (HASH(bp) <= HASH(root)))){
			//if(size <= root_size){
				if(GET_LCO(root) == ((unsigned int)(bp - heap_listp)))
					break;
				if(GET_LCO(root) == 0){
					printf("ERROR: try to delete a non-existing node! %lx\n", (unsigned long)bp);
					exit_from_error();
				}
				root = heap_listp + GET_LCO(root);
				continue;
			}
			else{
				if(GET_RCO(root) == ((unsigned int)(bp - heap_listp))){
					lr_flag = 1;
					break;
				}
				if(GET_RCO(root) == 0){
					printf("ERROR: try to delete a non-existing node! %lu\n", (unsigned long)bp);
					exit_from_error();
				}
				root = heap_listp + GET_RCO(root);
				continue;
			}
		}
	}

	//found: now root point to bp's parent if not root_flag
	//the following code takes text book 'Data Structure and Algorithm' (page 119: BST delete) as reference
	unsigned int temppointer;	//offset: the node to replace bp
	unsigned int tempparent = 0;	//offset: the parent of temppointer
	unsigned int parent = root - heap_listp;	//offset: the parent to bp, if not root_flag
	unsigned int pointer = bp - heap_listp;	//offset: bp

	if(GET_LCO(bp) == 0){	//if the left tree of the node to be delete is empty
		temppointer = GET_RCO(bp);
	}
	else{	//search for the maximum node as the node to replace the node to be delete		
		temppointer = GET_LCO(bp);
		while(GET_RCO(O2P(temppointer)) != 0){
			tempparent = temppointer;
			temppointer = GET_RCO(O2P(temppointer));	//descend from right
		}
		if(tempparent == 0)	//if the node to replace bp is its left child
			PUT_LCO(O2P(pointer), GET_LCO(O2P(temppointer)));
		else
			PUT_RCO(O2P(tempparent), GET_LCO(O2P(temppointer)));
		PUT_LCO(O2P(temppointer), GET_LCO(O2P(pointer)));
		PUT_RCO(O2P(temppointer), GET_RCO(O2P(pointer)));
	}

	//replace the node to be delete (bp) by the node to replace bp (temppointer)
	if(root_flag == 1){
		if(temppointer == 0)
			free_listp = NULL;
		else
			free_listp = O2P(temppointer);
	}
	else if(lr_flag == 0)
		PUT_LCO(O2P(parent), temppointer);
	else
		PUT_RCO(O2P(parent), temppointer);

	//mm_checkheap(449);
	return;
}

/*********************************************************
 * place - Place block of asize bytes at start of        *
 * free block bp and split if remainder would be         *
 * at least minimum block size                           *
 *********************************************************/
static void place(void *bp, size_t asize){	//checked
	//printf("place called, bp = %lu, asize = %u\n", (unsigned long)bp, (unsigned)asize);
	//mm_checkheap(460);

	size_t csize = GET_SIZE(HDRP(bp));
	bst_delete(bp);
	
	unsigned int dif = (long unsigned)csize - (long unsigned)asize;
	if(dif >= QSIZE){	//enough for split
		PUT(HDRP(bp), PACK(asize, 1, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0, 1));
		PUT(FTRP(bp), PACK(csize - asize, 0, 1));
		bst_add(bp);
	}
	else{	//not enough for split
		PUT(HDRP(bp), PACK(csize, 1, 1));
		bp = NEXT_BLKP(bp);
		SET_PREV_ALLOC1(bp, 1);
	}

	//mm_checkheap(479);
	return;
}

/*********************************************************
 * find_fit - Find a fit for a block with asize bytes    * 
 *********************************************************/
static void *find_fit(size_t asize){	//checked
	//printf("find_fit called, asize = %u\n", (unsigned)asize);
	//mm_checkheap(488);

	void *bp = free_listp;
	void *candidate = NULL;
	
	//search for the best fit block
	while(bp != NULL){
		size_t bpsize = GET_SIZE(HDRP(bp));
		if(bpsize == asize){	//perfectly fit
			candidate = bp;
			break;
		}
		else if(bpsize < asize){	//not enough
			if(GET_RCO(bp) == 0)
				break;
			bp = O2P(GET_RCO(bp));
			continue;
		}
		//enough
		candidate = bp;
		if(GET_LCO(bp) == 0)
			break;
		bp = O2P(GET_LCO(bp));
	}
	
	//now candidate point to the best fit block if not NULL
	//mm_checkheap(514);
	return candidate;
}

/*********************************************************
 * realloc - Change the size of the block by mallocing a *
 * new block, copying its data, and freeing the old block*
 *********************************************************/
void *realloc(void *oldptr, size_t size){
	//printf("realloc called, oldptr = %lu, size = %u\n", (unsigned long)oldptr, (unsigned)size);	

	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if(size == 0){
		free(oldptr);
		return 0;
	}

	/* If oldptr is NULL, then this is just malloc. */
	if(oldptr == NULL){
		return malloc(size);
	}

	newptr = malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if(!newptr){
		return 0;
	}

	/* Copy the old data. */
	oldsize = *SIZE_PTR(oldptr);
	if(size < oldsize)
		oldsize = size;
	memcpy(newptr, oldptr, oldsize);

	/* Free the old block. */
	free(oldptr);

	return newptr;
}

/*********************************************************
 * calloc - you may want to look at mm-naive.c           *
 * This function is not tested by mdriver, but it is     *
 * needed to run the traces.                             *
 *********************************************************/
void *calloc(size_t nmemb, size_t size){
	//printf("calloc called, nmemb = %u, size = %u\n", (unsigned)nmemb, (unsigned)size);

	size_t bytes = nmemb * size;
	void *newptr;

	newptr = malloc(bytes);
	memset(newptr, 0, bytes);

	return newptr;
}

/*********************************************************
 * Return whether the pointer is in the heap.            *
 * May be useful for debugging.                          *
 *********************************************************/
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*********************************************************
 * Return whether the pointer is aligned.                *
 * May be useful for debugging.                          *
 *********************************************************/
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*********************************************************
 * Optimize the case when large number of malloc reqs of *
 * same size happens, otherwise BST will become a list   *
 * and have terrible throughput. Our make-do solution is *
 * to use address comparison to be a substitude of size  *
 * comparison. Implementation with hash techneque. Better*
 * solution should maintain a list when same size.       *
 *********************************************************/
inline unsigned int hash(void* p){
	/*unsigned int table[64] = {3, 47, 22, 31, 14, 15, 7, 62, 
				26, 16, 28, 27, 17, 13, 45, 60,
				24, 8, 5, 12, 58, 47, 38, 53, 
				0, 30, 9, 25, 43, 37, 32, 19, 
				41, 52, 71, 62, 81, 33, 55, 50,
				2, 11, 49, 10, 20, 6, 53, 21, 
				18, 19, 54, 1, 23, 4, 29, 39,
				81, 37, 62, 18, 77, 72, 79, 70};
	return table[HASH(p)];*/
	return (HASH(p) * HASH(p)) % 1973;
}

/******************************************************************************************************
 *                                    Heap Checker with Helpers                                       *
 ******************************************************************************************************/
//unsigned long blkp[100000];	//only for debug use (checkheap), will be deleted when finish debugging

/*********************************************************
 * mm_checkheap                                          *
 *********************************************************/
void mm_checkheap_traverse(void *bp){
	if(bp == NULL)
		return;
	if(GET_LCO(bp))
		mm_checkheap_traverse(O2P(GET_LCO(bp)));
	printf("BST INFO: bp = %lx\n", (unsigned long)bp);
	if(GET_RCO(bp))
		mm_checkheap_traverse(O2P(GET_RCO(bp)));
	return;
}

void mm_checkheap(int lineno){
	//block check, iterate through implicitly
	void *bp = heap_listp;
	printf("checkheap called from line %d\n", lineno);
	while(1){
		int size = GET_SIZE(HDRP(bp));
		int alloc = GET_ALLOC(HDRP(bp));
		int prev_alloc = GET_PREV_ALLOC(HDRP(bp));
		printf("BLOCK INFO: bp = %lx, size = %u, alloc = %u, prev_alloc = %u\n", 
			(unsigned long)bp, (unsigned)size, alloc, prev_alloc);
		if(!alloc){
			printf("	lco = %u, rco = %u\n", (unsigned)GET_LCO(bp), (unsigned)GET_RCO(bp));
			printf("	lcp = %lx, rcp = %lx\n", (unsigned long)heap_listp + GET_LCO(bp), 
				(unsigned long)heap_listp + GET_RCO(bp));
		}
		if(size == 0)	//epilogue
			break;
		bp = NEXT_BLKP(bp);
	}

	//BST check
	printf("BST INFO: free_listp = %lx\n", (unsigned long)free_listp);
	mm_checkheap_traverse(free_listp);
 
	printf("\n\n");
	//char c;
	//int a = scanf("%c", &c);
	//a = a;	//keep gcc happy
	return;
}

/*********************************************************
 *                  exit from error                      * 
 *********************************************************/
void exit_from_error(){
	printf("Press any key to exit.\n");
	mm_checkheap(646);
	exit(0);
}

/******************************************************************************************************
 *                                             THE END                                                *
 * For more infomation, feel free to email me at zhaotianyang@pku.edu.cn.                             *
 ******************************************************************************************************/
