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
    "None",
    /* First member's full name */
    "None",
    /* First member's email address */
    "None",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define FSIZE 16

#define CHUNKSIZE0 (1 << 6)
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_TAG(p) (GET(p) & 0x2)
#define PUT_WITH_TAG(p, val) (*(unsigned int *)(p) = (val) | GET_TAG(p))

/* Adjust the reallocation tag */
#define SET_TAG(p) (*(unsigned int *)(p) = GET(p) | 0x2)
#define UNSET_TAG(p) (*(unsigned int *)(p) = GET(p) & ~0x2)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

#define BUFFER (1 << 7)

static void *extend_heap(size_t words);
// static void *next_fit(size_t asize);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);

static char *heap_listp = 0;
static char *pre_listp = 0;

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1));       /* Prologue header */
    PUT(heap_listp + DSIZE, PACK(DSIZE, 1));       /* Prologue footer */
    PUT(heap_listp + (DSIZE + WSIZE), PACK(0, 1)); /* Epilogue header */
    heap_listp += DSIZE;
    pre_listp = heap_listp;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE0 / WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{
    void *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    // size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    size = ALIGN(words);
    if ((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void place(void *bp, size_t asize)
{
    size_t size = GET_SIZE(HDRP(bp));
    size_t remain = size - asize;

    if (remain >= (FSIZE))
    {
        PUT_WITH_TAG(HDRP(bp), PACK(asize, 1));
        PUT_WITH_TAG(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(remain, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(remain, 0));
    }
    else
    {
        PUT_WITH_TAG(HDRP(bp), PACK(size, 1));
        PUT_WITH_TAG(FTRP(bp), PACK(size, 1));
    }
    // pre_listp = bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    if (!bp)
        return;

    size_t size = GET_SIZE(HDRP(bp));
    // 取消下个块的realloc标签
    UNSET_TAG(HDRP(NEXT_BLKP(bp)));

    PUT_WITH_TAG(HDRP(bp), PACK(size, 0));
    PUT_WITH_TAG(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    // prev要加一个判断，如果realloc了(有tag)就不合并
    size_t prev_alloc = (GET_ALLOC(FTRP(PREV_BLKP(bp)))) | GET_TAG(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        // Case 1: 前后都被分配了
        return bp;
    }

    if (prev_alloc && !next_alloc)
    {
        /* Case 2: prev is allocated, next block is free */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT_WITH_TAG(HDRP(bp), PACK(size, 0));
        PUT_WITH_TAG(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc)
    {
        /* Case 3: next is allocated, prev block is free */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT_WITH_TAG(FTRP(bp), PACK(size, 0));
        PUT_WITH_TAG(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else
    { /* Case 4: 前后都空闲，一起合并da */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT_WITH_TAG(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT_WITH_TAG(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    pre_listp = bp;
    return bp;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;       /* Adjusted block size */
    size_t extend_size; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = FSIZE;
    else
        asize = DSIZE * ((size + (FSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extend_size = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extend_size)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void *mm_realloc(void *ptr, size_t size)
{
    size_t adjust_size = size;
    // size_t old_size = GET_SIZE(HDRP(ptr));
    void *newptr = ptr;
    // size_t copySize;
    int remain, extend_size, buffer_size;

    if (size == 0)
    {
        return NULL;
    }
    if (adjust_size <= DSIZE)
        adjust_size = FSIZE;
    else
        adjust_size = DSIZE * ((adjust_size +(FSIZE - 1)) / DSIZE);

    adjust_size += BUFFER;
    buffer_size = GET_SIZE(HDRP(ptr)) - adjust_size;

    if (buffer_size < 0)
    {
        /* Check if next block is a free block or the epilogue block */
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr))))
        {
            remain = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - adjust_size;
            if (remain < 0)
            {
                extend_size = MAX(-remain, CHUNKSIZE);
                if (extend_heap(extend_size) == NULL)
                    return NULL;
                remain += extend_size;
            }

            // Do not split block
            PUT(HDRP(ptr), PACK(adjust_size + remain, 1)); /* Block header */
            PUT(FTRP(ptr), PACK(adjust_size + remain, 1)); /* Block footer */
        }
        else
        {
            newptr = mm_malloc(adjust_size - DSIZE);
            memmove(newptr, ptr, MIN(size, adjust_size));
            mm_free(ptr);
        }
        buffer_size = GET_SIZE(HDRP(newptr)) - adjust_size;
    }

    if (buffer_size < 2 * BUFFER)
        SET_TAG(HDRP(NEXT_BLKP(newptr)));
    return newptr;
}

static void *find_fit(size_t asize)
{
    //直接改动pre_listp是91, 新开一个cur_listp，pre_listp不变可以92
    /* Next fit */
    char *cur_listp = pre_listp;

    /* Search from the pre_listp to the end of list */
    while (GET_SIZE(HDRP(cur_listp)) > 0)
    {
        if ((!GET_ALLOC(HDRP(cur_listp)) && (asize <= GET_SIZE(HDRP(cur_listp)))) && !(GET_TAG(HDRP(cur_listp))))
            return cur_listp;
        cur_listp = NEXT_BLKP(cur_listp);
    }

    /* search from start of list to old pre_listp */
    for (cur_listp = heap_listp; cur_listp < pre_listp; cur_listp = NEXT_BLKP(cur_listp))
        if ((!GET_ALLOC(HDRP(cur_listp)) && (asize <= GET_SIZE(HDRP(cur_listp)))) && !(GET_TAG(HDRP(cur_listp))))
            return cur_listp;

    return NULL; /* no fit found */
}
// static void *next_fit(size_t size)
// {
//     void *bp;
//     void *min = pre_listp;
//     int extra = 50;
//     for (; GET_SIZE(HDRP(min)) > 0; min = NEXT_BLKP(min))
//     {
//         if (!GET_ALLOC(HDRP(min)) && (size <= GET_SIZE(HDRP(min))))
//         {
//             break;
//         }
//     }
//     int count = 0;
//     for (bp = pre_listp; GET_SIZE(HDRP(bp)) > 0 && count < extra; bp = NEXT_BLKP(bp))
//     {
//         count++;
//         if (!GET_ALLOC(HDRP(bp)) && (size <= GET_SIZE(HDRP(bp))))
//         {
//             if (GET_SIZE(HDRP(min)) > GET_SIZE(HDRP(bp)))
//             {
//                 min = bp;
//             }
//         }
//     }

//     bp = min;

//     if (!GET_ALLOC(HDRP(min)) && (size <= GET_SIZE(HDRP(min))))
//     {
//         pre_listp = bp;
//         return bp;
//     }

//     for (min = heap_listp; GET_SIZE(HDRP(min)) > 0; min = NEXT_BLKP(min))
//     {
//         if (!GET_ALLOC(HDRP(min)) && (size <= GET_SIZE(HDRP(min))))
//         {
//             break;
//         }
//     }

//     count = 0;

//     for (bp = pre_listp; GET_SIZE(HDRP(bp)) > 0 && count < extra; bp = NEXT_BLKP(bp))
//     {
//         count++;
//         if (!GET_ALLOC(HDRP(bp)) && (size <= GET_SIZE(HDRP(bp))))
//         {
//             if (GET_SIZE(HDRP(min)) > GET_SIZE(HDRP(bp)))
//             {
//                 min = bp;
//             }
//         }
//     }

//     bp = min;

//     if (!GET_ALLOC(HDRP(min)) && (size <= GET_SIZE(HDRP(min))))
//     {
//         pre_listp = bp;
//         return bp;
//     }

//     return NULL; /* No fit */
// }
