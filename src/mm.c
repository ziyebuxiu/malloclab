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
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

#define NEXT_FREEP(bp) (*(char **)(bp))
#define PREV_FREEP(bp) (*(char **)((char *)(bp) + WSIZE))

#define DEBUG 0
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *next_fit(size_t size);
static void add_to_freelist(void *bp);
static void remove_from_freelist(void *bp);

static char *heap_listp = 0;
static char *pre_listp = 0;
static char *free_listp = 0;

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);
    pre_listp = heap_listp;
    free_listp = NULL;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap((CHUNKSIZE) / WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */

    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    pre_listp = bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    if (prev_alloc && next_alloc)
    {
        // add_to_freelist(bp);
        return bp;
    }
    else if (!prev_alloc && next_alloc)
    {
        // remove_from_freelist(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else if (prev_alloc && !next_alloc)
    {
        // remove_from_freelist(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else
    {
        // remove_from_freelist(PREV_BLKP(bp));
        // remove_from_freelist(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // add_to_freelist(bp);
    pre_listp = bp;
    return bp;
}
static void *find_fit(size_t asize)
{
    char *bp;
    for (bp = free_listp; bp != NULL; bp = NEXT_FREEP(bp))
    {
        if (asize <= GET_SIZE(HDRP(bp)))
        {
            return bp;
        }
    }
    return NULL;
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = next_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void *mm_realloc(void *ptr, size_t size)
{
    void *newptr = ptr;

    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }
    if (DEBUG)
    {
        // 内存对齐
        size_t adjust_size;
        if (size <= DSIZE)
            adjust_size = 2 * DSIZE;
        else
            adjust_size = ALIGN(size);

        // 若size小于原来块大小，直接返回原来的块
        size_t old_size = GET_SIZE(HDRP(ptr));
        int remain = (GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr)))) - adjust_size;
        if (adjust_size <= old_size)
        {
            return ptr;
        }
        // 否则:检查物理后继是否free
        else if ((!GET_ALLOC(HDRP(NEXT_BLKP(ptr)))) || (!GET_SIZE(HDRP(NEXT_BLKP(ptr)))))
        {
            if (GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) < adjust_size)
            {
                if (extend_heap(MAX(CHUNKSIZE, -remain)) == NULL)
                {
                    return NULL;
                }
                remain += MAX(-remain, CHUNKSIZE);
            }
            // 从空闲表里删除
            // delete (NEXT_BLKP(ptr));
            PUT(HDRP(ptr), adjust_size + remain + 1);
            PUT(FTRP(ptr), adjust_size + remain + 1);
        }
        // 没有新的可用连续空闲块，申请新的空闲块
        else
        {
            newptr = mm_malloc(size);
            // printf("ptr: %d\n", ptr);
            memmove(newptr, ptr, GET_SIZE(HDRP(ptr)) - WSIZE);
            // printf("newptr2: %d\n", newptr);
            mm_free(ptr);
        }
    }

    else
    {
        size_t adjust_size = ALIGN(size);
        size_t old_size = GET_SIZE(HDRP(ptr));
        if (adjust_size < old_size)
        {
            return ptr;
        }
        size_t copySize;
        newptr = mm_malloc(size);
        if (newptr == NULL)
            return NULL;
        size = GET_SIZE(HDRP(ptr));
        copySize = GET_SIZE(HDRP(newptr));
        if (size < copySize)
            copySize = size;
        memmove(newptr, ptr, copySize - WSIZE);
        mm_free(ptr);
    }
    printf("ptr: %p\n", ptr);
    printf("newptr2: %p\n", newptr);
    return newptr;
}

static void *next_fit(size_t size)
{
    void *bp;
    void *min = pre_listp;
    int extra = 50;
    for (; GET_SIZE(HDRP(min)) > 0; min = NEXT_BLKP(min))
    {
        if (!GET_ALLOC(HDRP(min)) && (size <= GET_SIZE(HDRP(min))))
        {
            break;
        }
    }
    int count = 0;
    for (bp = pre_listp; GET_SIZE(HDRP(bp)) > 0 && count < extra; bp = NEXT_BLKP(bp))
    {
        count++;
        if (!GET_ALLOC(HDRP(bp)) && (size <= GET_SIZE(HDRP(bp))))
        {
            if (GET_SIZE(HDRP(min)) > GET_SIZE(HDRP(bp)))
            {
                min = bp;
            }
        }
    }

    bp = min;

    if (!GET_ALLOC(HDRP(min)) && (size <= GET_SIZE(HDRP(min))))
    {
        pre_listp = bp;
        return bp;
    }

    for (min = heap_listp; GET_SIZE(HDRP(min)) > 0; min = NEXT_BLKP(min))
    {
        if (!GET_ALLOC(HDRP(min)) && (size <= GET_SIZE(HDRP(min))))
        {
            break;
        }
    }

    count = 0;

    for (bp = pre_listp; GET_SIZE(HDRP(bp)) > 0 && count < extra; bp = NEXT_BLKP(bp))
    {
        count++;
        if (!GET_ALLOC(HDRP(bp)) && (size <= GET_SIZE(HDRP(bp))))
        {
            if (GET_SIZE(HDRP(min)) > GET_SIZE(HDRP(bp)))
            {
                min = bp;
            }
        }
    }

    bp = min;

    if (!GET_ALLOC(HDRP(min)) && (size <= GET_SIZE(HDRP(min))))
    {
        pre_listp = bp;
        return bp;
    }

    return NULL; /* No fit */
}
static void add_to_freelist(void *bp)
{
    NEXT_FREEP(bp) = free_listp;
    PREV_FREEP(bp) = NULL;
    if (free_listp != NULL)
    {
        PREV_FREEP(free_listp) = bp;
    }
    free_listp = bp;
}

static void remove_from_freelist(void *bp)
{
    if (PREV_FREEP(bp))
    {
        NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp);
    }
    else
    {
        free_listp = NEXT_FREEP(bp);
    }
    if (NEXT_FREEP(bp))
    {
        PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp);
    }
}