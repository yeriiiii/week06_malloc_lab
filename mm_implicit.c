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
    "Team 4",
    /* First member's full name */
    "Yerin Park",
    /* First member's email address */
    "yerina98@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

// /* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8

// /* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* MACRO */
/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
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

static void *heap_listp; // prologue 블럭을 가리키는 포인터
static void *lastp;

// 인접한 free block과 연결하기
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // [case1] prev: alloc, next: alloc //
    if (prev_alloc && next_alloc)
    {
        lastp = bp;
        return bp;
    }

    // [case2] prev: alloc, next: free //
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // [case3] prev: free, next: alloc //
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // [case4] prev: free, next: free //
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    lastp = bp;
    return bp;
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

static void *extend_heap(size_t words)
{
    void *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL; // mem_brk를 size만큼 늘리기

    /* Initialize free block header/footer and the eplilogue header */
    PUT(HDRP(bp), PACK(size, 0));         // old epilogue 영역을 new free block의 header로 초기화
    PUT(FTRP(bp), PACK(size, 0));         // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // new epilogue

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

// First-fit
static void *find_first_fit(size_t asize)
{
    /* First-fit search */
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) //
        {
            return bp;
        }
    }
    return NULL; /* No fit */
}

static void *find_next_fit(size_t asize)
{
    /* Next-fit search */
    void *bp = lastp;
    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) //
        {
            lastp = bp;
            return bp;
        }
    }
    bp = heap_listp;
    while (bp < lastp)
    {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) //
        {
            lastp = bp;
            return bp;
        }
    }
    return NULL; /* No fit */
}

static void *find_best_fit(size_t asize)
{
    /* Best-fit search */
    void *bp;
    size_t min_size = 1e9;
    void *min_bp = NULL;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)))
        { /* Best fit이 없을 때를 대비해서 asize보다 큰 최소 블럭(Second Best)을 계속 업데이트*/
            if (min_size > GET_SIZE(HDRP(bp)) && asize < GET_SIZE(HDRP(bp)))
            {
                min_size = GET_SIZE(HDRP(bp));
                min_bp = bp;
            }
            if (asize == GET_SIZE(HDRP(bp))) /* Best fit */
                return bp;
        }
    }
    return min_bp; /* Best fit이 없을 때 */
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // current size = 할당을 위해 선택된 현재 블럭의 크기

    if ((csize - asize) >= (2 * DSIZE)) // 선택된 현재 블럭을 분할할 수 있을 때
    {
        PUT(HDRP(bp), PACK(asize, 1)); // asize 크기의 블럭 할당
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0)); // 남은 부분은 free block으로 반환
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 쪼갤 수 없을 때 - csize 크기의 블럭 할당
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

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

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    lastp = heap_listp;

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amound to extend heap if no fit */
    void *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust blck size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_next_fit(asize)) != NULL) // find_first_fit or find_next_fit or find_best_fit
    {
        place(bp, asize);
        lastp = bp;
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    lastp = bp;
    return bp;
}

// int newsize = ALIGN(size + SIZE_T_SIZE);
// void *p = mem_sbrk(newsize);
// if (p == (void *)-1)
// return NULL;
// else {
//     *(size_t *)p = size;
//     return (void *)((char *)p + SIZE_T_SIZE);
// }

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    size_t old_size = GET_SIZE(HDRP(bp));
    size_t new_size = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    int diff = old_size - new_size;
    // new_size가 old_size보다 작거나 같으면 기존 bp 그대로 사용, 뒤에 남은 공간은 2DSIZE보다 크면 쪼개기
    if (0 <= diff)
    {
        return bp;
    }
    else if (diff >= 2 * DSIZE) // if (new_size <= old_size)
    {
        void *prev = bp;
        PUT(HDRP(bp), PACK(new_size, 1));
        PUT(FTRP(bp), PACK(new_size, 1));
        bp = FTRP(bp) + DSIZE;
        PUT(HDRP(bp), PACK(diff, 0));
        PUT(FTRP(bp), PACK(diff, 0));
        coalesce(bp);
        return prev;
    }
    else // new_size가 old_size보다 크면 사이즈 변경
    {
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t current_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        if (!next_alloc && current_size >= new_size) // next block이 가용 상태이고, old, next block의 사이즈 합이 new_size보다 크면 바로 합쳐서 쓰기
        {
            PUT(HDRP(bp), PACK(current_size, 1));
            PUT(FTRP(bp), PACK(current_size, 1));
            return bp;
        }
        else // 그렇지 않은 경우, 새로 block을 할당하기
        {
            void *new_bp = mm_malloc(new_size);
            place(new_bp, new_size);
            memcpy(new_bp, bp, old_size); // bp에서 new_size만큼의 영역을 복사해서 new_bp에 넣기
            mm_free(bp);
            return new_bp;
        }
    }
}