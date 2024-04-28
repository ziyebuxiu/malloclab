void *mm_realloc(void *ptr, size_t size)
{ // 如果 ptr == NULL 直接分配
    if (ptr == NULL)
        return mm_malloc(size); // 如果 size == 0 就释放
    else if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }
    size_t adjust_size = ALIGN(size), old_size = GET_SIZE(HDRP(ptr));
    size_t mv_size = MIN(adjust_size, old_size);
    char *oldptr = ptr;
    char *newptr;
    if (old_size == adjust_size)
        return ptr;
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t next_size = GET_SIZE(NEXT_BLKP(ptr));
    char *next_bp = NEXT_BLKP(ptr);
    size_t total_size = old_size;
    if (prev_alloc && !next_alloc && (old_size + next_size >= adjust_size))
    { // 后空闲
        total_size += next_size;
        delete_free_block(next_bp);
        PUT(HDRP(ptr), PACK(total_size, 1));
        PUT(FTRP(ptr), PACK(total_size, 1));
        place(ptr, total_size);
    }
    else if (!next_size && adjust_size >= old_size)
    { // 如果后部是结尾块，则直接 extend_heap
        size_t extend_size = adjust_size - old_size;
        if ((long)(mem_sbrk(extend_size)) == -1)
            return NULL;
        PUT(HDRP(ptr), PACK(total_size + extend_size, 1));
        PUT(FTRP(ptr), PACK(total_size + extend_size, 1));
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));
        place(ptr, adjust_size);
    }
    else
    { // 直接分配
        newptr = mm_malloc(adjust_size);
        if (newptr == NULL)
            return NULL;
        memcpy(newptr, ptr, MIN(old_size, size));
        mm_free(ptr);
        return newptr;
    }
    return ptr;
}