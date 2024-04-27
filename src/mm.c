/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is 1 by simply incrementing
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

#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */
#define CHUNKSIZE0 (1 << 6)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

/* Pack a size and 1 bit into a word */
#define PACK(size, alloc) ((size) | (alloc))
#define PACK_ALL(size, prev_alloc, alloc) ((size) | (prev_alloc) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned *)(p))
#define PUT(p, val) (*(unsigned *)(p) = (val))

/* Read the size and 1 fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PREV_ALLOC(p) (GET(p) & 0x2)
#define SET_ALLOC(p) (GET(p) |= 0x1)
#define SET_FREE(p) (GET(p) &= ~0x1)
#define SET_PREV_ALLOC(p) (GET(p) |= 0x2)
#define SET_PREV_FREE(p) (GET(p) &= ~0x2)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp))))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

#define NEXT_FREEP(bp) (*(char **)(bp))
#define PREV_FREEP(bp) (*(char **)((char *)(bp) + WSIZE))

// 空链最大个数
#define MAXNUM 16
#define DEBUG 0

// 遍历空链表
#define PREV_NODE(bp) ((char *)(mem_heap_lo() + *(unsigned *)(bp)))
#define NEXT_NODE(bp) ((char *)(mem_heap_lo() + *(unsigned *)(bp + WSIZE)))
#define SET_NODE_PREV(bp, val) (*(unsigned *)(bp) = ((unsigned)(long)val))
#define SET_NODE_NEXT(bp, val) (*(unsigned *)((char *)bp + WSIZE) = ((unsigned)(long)val))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *next_fit(size_t size);
static void insert(void *ptr, size_t size);
static void delete(void *ptr);
static size_t adjust_size(size_t size);

static char *heap_listp = 0;
static char *pre_listp = 0;
static char **free_listp = 0; // 空链表的头指针

void insert(void *ptr, size_t size)
{
    int index = 0;
    size_t tmp_size = size;
    while ((index < MAXNUM) && (size > 1))
    {
        tmp_size >>= 1;
        index++;
    }
    char *curp = free_listp[index];
    free_listp[index] = ptr;
    if (curp != mem_heap_lo())
    {
        SET_NODE_PREV(ptr, NULL);
        SET_NODE_NEXT(ptr, curp);
        SET_NODE_PREV(curp, ptr);
    }
    else
    {
        SET_NODE_PREV(ptr, NULL);
        SET_NODE_NEXT(ptr, NULL);
    }
}

void delete(void *ptr)
{
    printf("delete start...\n");
    size_t size = GET_SIZE(HDRP(ptr));
    int index = 0;
    printf("size: %d\n", size);
    while ((index < MAXNUM) && (size > 1))
    {
        size >>= 1;
        index++;
    }
    printf("index: %d\n", index);
    char *prev = PREV_NODE(ptr);
    char *next = NEXT_NODE(ptr);
    printf("mem heap lo: %p\n", mem_heap_lo());
    printf("start prev: %p\n start next: %p\n", prev, next);
    // 头结点
    if (prev == mem_heap_lo())
    {
        printf("111\n");
        free_listp[index] = next;
        if (next != mem_heap_lo()){
            printf("222\n");
            
            SET_NODE_PREV(next, NULL);
            // printf("catch you!\n");
        }
            
    }
    else
    {
        printf("333\n");
        SET_NODE_NEXT(prev, next);
        if (next != mem_heap_lo()){
            printf("444\n");
            SET_NODE_PREV(next, NULL);
        }
            
    }
    printf("end prev: %p\n end next: %p\n", prev, next);
    
}
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    free_listp = mem_heap_lo(); // 初始化空链表
    int i = 0;
    for (i = 0; i < MAXNUM; i++)
    {
        // 开辟尺寸为DSIZE的块，存储空链表当前的头指针
        if ((heap_listp = mem_sbrk(2 * WSIZE)) == (void *)-1)
            return -1;
        free_listp[i] = mem_heap_lo();
    }
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);
    pre_listp = heap_listp;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap((CHUNKSIZE0) / WSIZE) == NULL)
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
    size_t prev_blk = GET_PREV_ALLOC(HDRP(bp));
    // PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    // PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(bp), PACK_ALL(size, prev_blk, 0));
    PUT(FTRP(bp), PACK_ALL(size, prev_blk, 0));
    /* New epilogue header */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void place(void *bp, size_t asize)
{
    size_t cur_size = GET_SIZE(HDRP(bp));
    delete(bp);
    if ((cur_size - asize) >= (2 * DSIZE))
    {
        // 设置块头部
        //  PUT(HDRP(bp), PACK(asize, 1));
        //  PUT(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(bp), PACK_ALL(asize, GET_PREV_ALLOC(HDRP(bp)), 1));

        bp = NEXT_BLKP(bp);
        // PUT(HDRP(bp), PACK(cur_size - asize, 0));
        // PUT(FTRP(bp), PACK(cur_size - asize, 0));
        PUT(HDRP(bp), PACK_ALL(cur_size - asize, 2, 0));
        PUT(FTRP(bp), PACK_ALL(cur_size - asize, 2, 0));

        insert(bp, cur_size - asize);
    }
    else
    {
        // 改变标志位
        SET_ALLOC(HDRP(bp));
        // 分配块设置头部
        SET_PREV_ALLOC(HDRP(NEXT_BLKP(bp)));
        // 如果是空闲块
        if (!GET_ALLOC(HDRP(NEXT_BLKP(bp))))
        {
            SET_PREV_ALLOC(FTRP(NEXT_BLKP(bp)));
        }

        // PUT(HDRP(bp), PACK(cur_size, 1));
        // PUT(FTRP(bp), PACK(cur_size, 1));
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
        // case 1: prev和next都分配
        printf("case 1\n");
        SET_PREV_FREE(HDRP(NEXT_BLKP(bp)));
        // return bp;
    }
    else if (!prev_alloc && next_alloc)
    {
        // case 2: prev已分配next未分配
        printf("case 2\n");
        delete (PREV_BLKP(bp));
        SET_PREV_FREE(HDRP(NEXT_BLKP(bp)));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        size_t prev_prev_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK_ALL(size, prev_prev_alloc, 0));
        PUT(FTRP(bp), PACK_ALL(size, prev_prev_alloc, 0));
        bp = PREV_BLKP(bp);
    }
    else if (prev_alloc && !next_alloc)
    {
        // case 3: prev未分配next已分配
        printf("case 3:\n");
        delete(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK_ALL(size, 2, 0));
        // 此处已经更新头部，下一个块已经指向分配块了，不能以 NEXT_BLKP(bp) 访问
        PUT(FTRP(bp), PACK_ALL(size, 2, 0));
    }
    else
    {
        // case 4: prev,next都未分配
        delete (NEXT_BLKP(bp));
        delete (PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert(bp, size);
    pre_listp = bp;
    return bp;
}

// first fit
static void *find_fit(size_t asize)
{
    int index = 0;
    size_t tmp_size = asize;
    while ((index < MAXNUM) && (asize > 1))
    {
        index++;
        tmp_size >>= 1;
    }

    char *bp;
    int i = 0;
    for (i = index; i < MAXNUM; i++)
    {
        bp = free_listp[i];
        while (bp != mem_heap_lo())
        {
            unsigned remain = GET_SIZE(HDRP(bp)) - tmp_size;
            if (remain >= 0)
                return bp;
            bp = NEXT_NODE(bp);
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
    // asize = adjust_size(size);
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
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
    printf("realloc start------------------------------\n");
    void *newptr = mm_malloc(size);

    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    size_t adjust_size = ALIGN(size);
    size_t old_size = MIN(size, GET_SIZE(HDRP(ptr)));
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

    // printf("ptr: %p\n", ptr);
    // printf("newptr2: %p\n", newptr);
    printf("realloc end------------------------------\n");
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
