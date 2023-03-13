/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* macros from book */
#define WSIZE		4
#define DSIZE		8
#define CHUNKSIZE	(1<<12)

#define ALLOCATED	1
#define FREE		0
#define PRI_ALLOCATED	2
#define PRI_FREE	0

#define	MAX(x, y)	((x) > (y)? (x) : (y))

#define PACK(size, prior_alloc, alloc)	((size) |(prior_alloc) | (alloc))

#define	GET(p)		(*(unsigned int *)(p))
#define	PUT(p, val)	(*(unsigned int *)(p) = (val))
#define GET_PTR(p)	(*((void *) *)(p))
#define PUT_PTR(p, ptr)	(*((void *) *)(p) = (ptr)) 

#define GET_SIZE(p)	(GET(p) & ~0x7)
#define GET_ALLOC(p)	(GET(p) & 0x1)
#define GET_PRI_ALLOC(p)	(GET(p) & 0x2)

#define	HDRP(bp)	((char *)(bp) - WSIZE)
#define FTRP(bp)	((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define	NEXT_BLKP(bp)	((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)	((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

typedef struct link_node{
	struct link_node *succ;
	struct link_node *pred;
}lnode;

static void *heap_listp;	// point to the bp of prologue block
static lnode *link_entry;	// point to the pointer array of link entry points

static int check_counts = 1;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static int bit_counts(size_t size);
static void insert_lnode(size_t size, void* bp);
static void remove_lnode(void* bp);

static void checker();
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
	// call mem_sbrk for 60 words
	if ((heap_listp = mem_sbrk(60*WSIZE)) == (void *)-1 )
		return -1;

	// 	first word for padding
	// 	28*2 words for link entry points, the array address stored in link_entry
	memset(heap_listp, 0, 57*WSIZE);

	// 	one word for prologue block header, one word for prologue payload. just for alignment
	PUT(heap_listp + (57*WSIZE), PACK(DSIZE, PRI_ALLOCATED, ALLOCATED));
	PUT(heap_listp + (58*WSIZE), 0);

	// 	one word for epilogue block header ( size=0, prior_status=allocated, status=allocated
	PUT(heap_listp + (59*WSIZE), PACK(0, PRI_ALLOCATED, ALLOCATED));

	// adjust the heap_listp, and set the link_entry
	link_entry = (lnode*)(heap_listp + WSIZE);
	heap_listp += (58*WSIZE);

	// then call extend_heap to extend the heap
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
		return -1;
	return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
	// judge that if the size is 0
	// the size should be an even number, and larger than or equal to 24 bytes(6 word)
	// call find_fit to find a block,
	// if couldn't find a free block, call extend_heap
	// call place to modify the header and the link
	size_t asize;
	size_t extendsize;
	char *bp;
	
	if (size == 0)
		return NULL;

	size = size + WSIZE;	// the allocated must have a header at least, i forget this before

	if ( size <= 4*WSIZE)
		asize = 4*WSIZE;
	else
		asize = DSIZE * ((size  + (DSIZE - 1)) / DSIZE);
	//printf("mm_malloc(size:%u bytes)\n", size);
	
	if ((bp = find_fit(asize)) != NULL)
	{
		place(bp, asize);
		//checker("mm_malloc");
		//printf("mm_malloc(ptr:%x, size:%d bytes)\n",bp, size);
		return bp;
	}

	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
		return NULL;
	place(bp, asize);
	//printf("mm_malloc(ptr:%x, size:%d bytes)\n",bp, size);
	//checker("mm_malloc");
	return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
	// set the status to 0 in the header and footer
	// call coalesce
	size_t size = GET_SIZE(HDRP(ptr));
	//printf("mm_free(ptr:%x, size:%d bytes)\n",ptr, size);	
	PUT(HDRP(ptr), PACK(size, GET_PRI_ALLOC(HDRP(ptr)), FREE));
	PUT(FTRP(ptr), PACK(size, GET_PRI_ALLOC(HDRP(ptr)), FREE));
	insert_lnode(size, ptr);
	coalesce(ptr);
	//checker("mm_free");
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
	// allocate a new pointer
	// copy the bytes to the new pointer
	// free the old pointer
	//printf("realloc ptr:%x, for %d bytes\n",ptr, size);
    	void *oldptr = ptr;
    	void *newptr;
    	size_t old_size = GET_SIZE(HDRP(oldptr));
	size_t asize;
	size_t fit_size;
	size_t split_size;

	size_t tmp1, tmp2, tmp3;
	tmp1 = GET(oldptr);
	tmp2 = GET(oldptr+4);
	tmp3 = GET(oldptr+old_size-4-4);
	//printf("mm_realloc: old_size=%u; ", old_size);
	if ( size <= 4*WSIZE)
		asize = 4*WSIZE;
	else
		asize = DSIZE * ((size  + (DSIZE - 1)) / DSIZE);
    
    	mm_free(oldptr);
	if ((newptr = find_fit(asize)) != NULL)
	{
		remove_lnode(newptr);
    		if (asize >= old_size)
		{
			PUT(newptr, tmp1);
			PUT(newptr+4, tmp2);
    			memmove(newptr+8, oldptr+8, old_size-8-4-4);
			PUT(newptr+old_size-4-4, tmp3);
		}
		else{
			PUT(newptr, tmp1);
			PUT(newptr+4, tmp2);
			memmove(newptr+8, oldptr+8, asize-8-4);
		}
		fit_size = GET_SIZE(HDRP(newptr));
		split_size = fit_size - asize;
		
		if ( split_size >= 16 )	// the min size is 16 bytes ( header = 4, footer = 4, predptr = 4, succptr = 4)
		{
			// now split the block
			PUT(HDRP(newptr), PACK(asize, GET_PRI_ALLOC(HDRP(newptr)), ALLOCATED));
		
			lnode *split = (lnode*)NEXT_BLKP(newptr);
			insert_lnode(split_size, split);
			PUT(HDRP(NEXT_BLKP(newptr)), PACK(split_size, PRI_ALLOCATED, FREE));	// set header and footer of the split block
			PUT(FTRP(NEXT_BLKP(newptr)), PACK(split_size, PRI_ALLOCATED, FREE));

			lnode *next = (lnode*)NEXT_BLKP(split);	// set the header and footer of the block behind the split block
			PUT(HDRP(next), PACK(GET_SIZE(HDRP(next)), PRI_FREE, GET_ALLOC(HDRP(next))));
			//PUT(FTRP(next), PACK(GET_SIZE(HDRP(next)), PRI_FREE, GET_ALLOC(HDRP(next))));
		}
		else{
			PUT(HDRP(newptr), PACK(fit_size, GET_PRI_ALLOC(HDRP(newptr)), ALLOCATED));
			// the header of next block records the status of current block. 
			// need to modify it
			PUT(HDRP(NEXT_BLKP(newptr)), PACK(GET_SIZE(HDRP(NEXT_BLKP(newptr))), PRI_ALLOCATED, GET_ALLOC(HDRP(NEXT_BLKP(newptr)))));
			//PUT(FTRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), PRI_ALLOCATED, GET_ALLOC(HDRP(NEXT_BLKP(bp)))));
		}	
			//checker("mm_malloc");
			//printf("mm_malloc(ptr:%x, size:%d bytes)\n",bp, size);
			checker("mm_realloc");
			return newptr;
	}

	size_t extendsize = MAX(asize, CHUNKSIZE);
	if ((newptr = extend_heap(extendsize/WSIZE)) == NULL)
		return NULL;
	
	remove_lnode(newptr);
    	if (asize >= old_size)
	{
		PUT(newptr, tmp1);
		PUT(newptr+4, tmp2);
    		memmove(newptr+8, oldptr+8, old_size-8-4-4);
		PUT(newptr+old_size-4-4, tmp3);
	}
	else{
		PUT(newptr, tmp1);
		PUT(newptr+4, tmp2);
		memmove(newptr+8, oldptr+8, asize-8-4);
	}
	fit_size = GET_SIZE(HDRP(newptr));
	split_size = fit_size - asize;
		
	if ( split_size >= 16 )	// the min size is 16 bytes ( header = 4, footer = 4, predptr = 4, succptr = 4)
	{
		// now split the block
		PUT(HDRP(newptr), PACK(asize, GET_PRI_ALLOC(HDRP(newptr)), ALLOCATED));
	
		
		lnode *split = (lnode*)NEXT_BLKP(newptr);
		insert_lnode(split_size, split);
		PUT(HDRP(NEXT_BLKP(newptr)), PACK(split_size, PRI_ALLOCATED, FREE));	// set header and footer of the split block
		PUT(FTRP(NEXT_BLKP(newptr)), PACK(split_size, PRI_ALLOCATED, FREE));

		lnode *next = (lnode*)NEXT_BLKP(split);	// set the header and footer of the block behind the split block
		PUT(HDRP(next), PACK(GET_SIZE(HDRP(next)), PRI_FREE, GET_ALLOC(HDRP(next))));
		//PUT(FTRP(next), PACK(GET_SIZE(HDRP(next)), PRI_FREE, GET_ALLOC(HDRP(next))));

	}
	else{
		PUT(HDRP(newptr), PACK(fit_size, GET_PRI_ALLOC(HDRP(newptr)), ALLOCATED));
		// the header of next block records the status of current block. 
		// need to modify it
		PUT(HDRP(NEXT_BLKP(newptr)), PACK(GET_SIZE(HDRP(NEXT_BLKP(newptr))), PRI_ALLOCATED, GET_ALLOC(HDRP(NEXT_BLKP(newptr)))));
		//PUT(FTRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), PRI_ALLOCATED, GET_ALLOC(HDRP(NEXT_BLKP(bp)))));
	}	
	//printf("%d.mm_realloc: new ptr is %x\n", count++, newptr);
	checker("mm_realloc");
	//if (!memcmp(newptr, oldptr, copySize)
	//	printf("didn't preserve");
    	return newptr;
}


static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;

	// allocate an even number of words to maitain alignment
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

	// call mem_sbrk for more bytes
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;
	//memset(bp, 0, size);

	// turn the old epilogue header into a header of a new and free block, update the size and status, but keep the prior_status as before
	int pri_alloc = GET_PRI_ALLOC(HDRP(bp));
	PUT(HDRP(bp), PACK(size, pri_alloc, FREE));

	// set the footer for the free block
	PUT(FTRP(bp), PACK(size, pri_alloc, FREE));

	// find the proper link entry point, set the prev_ptr and the succ_ptr, using LIFO
	insert_lnode(size, bp);

	// set the epilogue header
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, PRI_FREE, ALLOCATED));

	// call coalesce for possible merge
	return coalesce(bp);
}

static void *coalesce(void *bp)
{
	size_t size = GET_SIZE(HDRP(bp));
	// read the status of prior block from the header of current block
	int pri_alloc = GET_PRI_ALLOC(HDRP(bp));

	// read the status of next block from the header of next block
	int next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

	// judge the requirement of merging
	if ( pri_alloc && next_alloc)
	{
		return bp;
	}
	else if (pri_alloc && !next_alloc)
	{
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		lnode *next = (lnode*)NEXT_BLKP(bp);
		
		remove_lnode(next);
		remove_lnode(bp);

		PUT(HDRP(bp), PACK(size, pri_alloc, FREE));
		PUT(FTRP(bp), PACK(size, pri_alloc, FREE));
	
		insert_lnode(size, bp);	
	}		
	else if (!pri_alloc && next_alloc)
	{
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		lnode *pri = (lnode*)PREV_BLKP(bp);
	
		remove_lnode(pri);
		remove_lnode(bp);

		PUT(HDRP(pri), PACK(size, GET_PRI_ALLOC(HDRP(pri)), FREE));
		PUT(FTRP(bp), PACK(size, GET_PRI_ALLOC(HDRP(pri)), FREE));
	
		bp = pri;
		insert_lnode(size, pri);
	}
	else
	{
		remove_lnode(PREV_BLKP(bp));
		remove_lnode(NEXT_BLKP(bp));
		remove_lnode(bp);

		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, GET_PRI_ALLOC(HDRP(PREV_BLKP(bp))),FREE));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, GET_PRI_ALLOC(HDRP(PREV_BLKP(bp))), FREE));

		bp = PREV_BLKP(bp);
		insert_lnode(size, bp);
	}
	return bp;
	// if needed, remove the prior or next block from its link
	// caculate the new size
	// put the new block into the link corresponding to the size, using LIFO
	// return new bp
}

static void *find_fit(size_t asize)
{
	// there're links for blocks of different size
	//	1-31, 32-63, 64-127.... 28 links and 28 entry points in total
	int range = bit_counts(asize);
	lnode *bp;
	int flag = 0;
	for ( ; range<28; range++)
	{
		bp = link_entry[range].succ;
		while(bp)
		{
			int c_size = GET_SIZE(HDRP(bp));
			int c_alloc = GET_ALLOC(HDRP(bp));
			if (c_size >= asize && c_alloc == FREE)
			{
				flag = 1;
				break;
			}
			bp = bp->succ;
		}
		if (flag)
			break;
	}
	if (flag)
		return bp;
	else
		return NULL;	
	// the range in which asize is located in is determined by doing right shifts in while loop
	// search in the corresponding link according to the specific range
	// if it is not found in the link, search in next link then
	// if couldn't find a proper free block, call extend_heap
	// return bp
}

static void place(void *bp, size_t asize)
{
	// get the block size
	// remove the block from the link
	// determine whether the block can be split 
	// modify the header:
	//	modify the size and status, but keep the prior_status
	// if need to split the block:
	//	set the header and footer of the new split block
	//	put it into the proper link using LIFO
//	printf("into place\n");
	int origin_size = 0;
	origin_size = GET_SIZE(HDRP(bp));

	int split_size = 0;
	split_size = origin_size - asize;
	if ( split_size >= 16 )	// the min size is 16 bytes ( header = 4, footer = 4, predptr = 4, succptr = 4)
	{
		// now split the block
		remove_lnode( bp);

		PUT(HDRP(bp), PACK(asize, GET_PRI_ALLOC(HDRP(bp)), ALLOCATED));
		
		
		lnode *split = (lnode*)NEXT_BLKP(bp);
		insert_lnode(split_size, split);
		PUT(HDRP(NEXT_BLKP(bp)), PACK(split_size, PRI_ALLOCATED, FREE));	// set header and footer of the split block
		PUT(FTRP(NEXT_BLKP(bp)), PACK(split_size, PRI_ALLOCATED, FREE));

		lnode *next = (lnode*)NEXT_BLKP(split);	// set the header and footer of the block behind the split block
		PUT(HDRP(next), PACK(GET_SIZE(HDRP(next)), PRI_FREE, GET_ALLOC(HDRP(next))));
		//PUT(FTRP(next), PACK(GET_SIZE(HDRP(next)), PRI_FREE, GET_ALLOC(HDRP(next))));

	}
	else{
		remove_lnode( bp);

		PUT(HDRP(bp), PACK(origin_size, GET_PRI_ALLOC(HDRP(bp)), ALLOCATED));
		
		// the header of next block records the status of current block. 
		// need to modify it
		PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), PRI_ALLOCATED, GET_ALLOC(HDRP(NEXT_BLKP(bp)))));
		//PUT(FTRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), PRI_ALLOCATED, GET_ALLOC(HDRP(NEXT_BLKP(bp)))));
	}	

}
static int bit_counts(size_t size)
{
	int entry_index = 0;
	while(1)
	{
		if ( (size >> (5 + entry_index)) == 0)
			break;
		entry_index++;
	}
	return entry_index;
}

static void insert_lnode(size_t size, void* bp)
{
	int entry_index = bit_counts(size) ;
	lnode* old_first = link_entry[entry_index].succ;
	lnode* c_lnode = (lnode *)bp;
	if ( old_first == NULL )
	{
		link_entry[entry_index].succ = bp;
		//	PUT_PTR(bp, NULL);
		//PUT_PTR(bp+DSIZE, NULL); 
		c_lnode->pred =(lnode*) &link_entry[entry_index];
		c_lnode->succ = NULL;
	}
	else
	{
		link_entry[entry_index].succ = bp;
		old_first->pred = bp;
		//PUT_PTR(bp, old_first);
		//PUT_PTR(bp+DSIZE, NULL);
		c_lnode->pred =(lnode*) &link_entry[entry_index];
		c_lnode->succ = old_first;
		
		//PUT_PTR(old_first+DSIZE, bp);
		//c_lnode->pred = bp;
	}
}

static void remove_lnode(void* bp)
{
	lnode *current = bp;
	current->pred->succ = current->succ;
	if ( current->succ != NULL)
	{
		current->succ->pred = current->pred;	
	}
	
}




static void checker(char* str)
{
	void *max_heap_addr;
	void *bp = heap_listp;
	int count = 1;

	printf("---------------checker called by %s, round %d ----------------\n",str, check_counts);
	while ( 1 )
	{

		max_heap_addr = mem_heap_hi() + 1;
		if ( bp >= max_heap_addr || GET_SIZE(HDRP(bp)) == 0)
			break;
		printf("\n-----block no.%d-----\n",count);
		if ( GET_ALLOC(HDRP(bp)) == ALLOCATED )
		{
			printf("status: ALLOCATED\n");
		}
		else{
			printf("status: FREE\n");
		}
		printf("size: %d\n", GET_SIZE(HDRP(bp)));
		printf("header at %x, bp at %x, footer(if exist) at %x\n", HDRP(bp), bp, FTRP(bp));
		printf("-----block no.%d-----\n", count);
		count ++;
		bp = NEXT_BLKP(bp);
	}
	printf("---------------checker called by %s, round %d ----------------\n",str,  check_counts ++ );

}



