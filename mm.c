#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"

/*********************************************************
 * Team information
 ********************************************************/
team_t team = {
    "TeamName",
    "Andrew Wood",
    "a---@colorado.edu",
    "",
    ""
};

/////////////////////////////////////////////////////////////////////////////
// Constants and macros
/////////////////////////////////////////////////////////////////////////////
#define WSIZE         4       /* Word size (bytes) */
#define DSIZE         8       /* Doubleword size (bytes) */
#define CHUNKSIZE     (1<<12) /* Initial heap size (bytes) */
#define OVERHEAD      8       /* Overhead of header and footer (bytes) */

/*
 * Minimum block size:
 * [HDR(4)][PAD(4)][PARENT(8)][LEFT(8)][RIGHT(8)][COLOR(8)][FTR(4)] = 44 bytes
 * Round up to a multiple of DSIZE:
 * MINBLOCKSIZE = 6*DSIZE = 48 bytes ensures enough space.
 */
#define MINBLOCKSIZE  (6*DSIZE)

static inline int MAX(int x, int y) { return x > y ? x : y; }

static inline uint32_t PACK(uint32_t size, int alloc) {
    return (size | (alloc & 0x1));
}

static inline uint32_t GET(void *p) { return *(uint32_t *)p; }
static inline void PUT(void *p, uint32_t val) { *((uint32_t *)p) = val; }

static inline uint32_t GET_SIZE(void *p) { return GET(p) & ~0x7; }
static inline int GET_ALLOC(void *p) { return GET(p) & 0x1; }

static inline void *HDRP(void *bp) {
    return (char *)(bp) - WSIZE;
}
static inline void *FTRP(void *bp) {
    return (char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE;
}
static inline void *NEXT_BLKP(void *bp) {
    return (char *)(bp) + GET_SIZE((char *)(bp) - WSIZE);
}
static inline void *PREV_BLKP(void *bp) {
    return (char *)(bp) - GET_SIZE((char *)(bp) - DSIZE);
}

/*
 * Red-Black Tree Node Layout in free block:
 * [HDR(4)][PAD(4)][PARENT(8)][LEFT(8)][RIGHT(8)][COLOR(8)][...][FTR(4)]
 *
 * bp points to start of free block payload (after HDR+PAD):
 *   PARENT(bp) at bp
 *   LEFT(bp) at bp+8
 *   RIGHT(bp) at bp+16
 *   COLOR(bp) at bp+24 (use first byte)
 */

#define PARENT_PTR(bp) ((char **)(bp))
#define LEFT_PTR(bp)   ((char **)((char *)(bp) + DSIZE))
#define RIGHT_PTR(bp)  ((char **)((char *)(bp) + 2*DSIZE))
#define COLOR_PTR(bp)  ((char *)((char *)(bp) + 3*DSIZE))

#define PARENT(bp) (*PARENT_PTR(bp))
#define LEFT(bp)   (*LEFT_PTR(bp))
#define RIGHT(bp)  (*RIGHT_PTR(bp))
#define COLOR(bp)  ((int)(*(unsigned char *)(COLOR_PTR(bp))))

#define SET_COLOR(bp, c) (*(unsigned char *)(COLOR_PTR(bp)) = (unsigned char)(c))

#define RED   1
#define BLACK 0

/////////////////////////////////////////////////////////////////////////////
// Global variables
/////////////////////////////////////////////////////////////////////////////

static char *heap_listp;  /* Pointer to first block */

/* NIL sentinel node */
static char nil_node[4*DSIZE]; /* Enough space to store pointers/color */
static void *NIL = (void *)nil_node;

static void *root;        /* Root of the RBT */

/*
 * Function prototypes
 */
int mm_init(void);
void *mm_malloc(uint32_t size);
void mm_free(void *bp);
void *mm_realloc(void *ptr, uint32_t size);

static void *extend_heap(uint32_t words);
static void place(void *bp, uint32_t asize);
static void *find_fit(uint32_t asize);
static void *coalesce(void *bp);
static void insert_free_block(void *bp, uint32_t size);
static void remove_free_block(void *bp);

/* RBT functions */
static void rbt_insert(void *bp);
static void rbt_insert_fixup(void *bp);
static void rbt_remove(void *bp);
static void rbt_remove_fixup(void *x);
static void *rbt_find_best_fit(void *node, uint32_t asize, void **best_fit);

static void *rbt_minimum(void *node);
static void left_rotate(void *x);
static void right_rotate(void *x);
static void rbt_transplant(void *u, void *v);

int mm_init(void)
{
    /* Initialize NIL node */
    PARENT(NIL) = NIL;
    LEFT(NIL) = NIL;
    RIGHT(NIL) = NIL;
    SET_COLOR(NIL, BLACK);

    root = NIL;

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(uint32_t words)
{
    char *bp;
    uint32_t size;

    size = (words % 2)? (words+1)*WSIZE : words*WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    uint32_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    uint32_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    uint32_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        // no merge
    } else if (prev_alloc && !next_alloc) {
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    } else if (!prev_alloc && next_alloc) {
        remove_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    } else {
        remove_free_block(PREV_BLKP(bp));
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }

    insert_free_block(bp, size);
    return bp;
}

static void insert_free_block(void *bp, uint32_t size) {
    (void)size; // Not needed directly
    PARENT(bp) = NIL;
    LEFT(bp) = NIL;
    RIGHT(bp) = NIL;
    SET_COLOR(bp, RED);
    rbt_insert(bp);
}

static void remove_free_block(void *bp) {
    rbt_remove(bp);
}

static void *find_fit(uint32_t asize) {
    void *best_fit = NULL;  // NULL indicates no fit found yet
    rbt_find_best_fit(root, asize, &best_fit);
    return best_fit; // If still NULL, no fit
}

static void place(void *bp, uint32_t asize)
{
    uint32_t csize = GET_SIZE(HDRP(bp));
    remove_free_block(bp);

    if ((csize - asize) >= MINBLOCKSIZE) {
        PUT(HDRP(bp), PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));

        void *new_bp = NEXT_BLKP(bp);
        PUT(HDRP(new_bp), PACK(csize-asize,0));
        PUT(FTRP(new_bp), PACK(csize-asize,0));

        insert_free_block(new_bp, csize-asize);
    } else {
        PUT(HDRP(bp), PACK(csize,1));
        PUT(FTRP(bp), PACK(csize,1));
    }
}

void *mm_malloc(uint32_t size)
{
    uint32_t asize;
    uint32_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size+(DSIZE)+(DSIZE-1))/DSIZE);

    asize = MAX(asize, MINBLOCKSIZE);

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

void mm_free(void *bp)
{
    if (bp == NULL)
        return;
    uint32_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    coalesce(bp);
}

void *mm_realloc(void *ptr, uint32_t size)
{
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    if (ptr == NULL) {
        return mm_malloc(size);
    }

    // Current block size (excluding header/footer)
    uint32_t old_size = GET_SIZE(HDRP(ptr)) - DSIZE;
    uint32_t asize;

    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size+(DSIZE)+(DSIZE-1))/DSIZE);

    asize = MAX(asize, MINBLOCKSIZE);

    // If the requested size is already smaller or equal to old_size,
    // we can simply return the same block.
    if (asize <= GET_SIZE(HDRP(ptr))) {
        // Consider splitting if there's a large enough remainder to form a free block
        uint32_t csize = GET_SIZE(HDRP(ptr));
        if ((csize - asize) >= MINBLOCKSIZE) {
            // Shrink the block
            PUT(HDRP(ptr), PACK(asize,1));
            PUT(FTRP(ptr), PACK(asize,1));
            void *new_bp = NEXT_BLKP(ptr);
            PUT(HDRP(new_bp), PACK(csize-asize,0));
            PUT(FTRP(new_bp), PACK(csize-asize,0));
            insert_free_block(new_bp, csize - asize);
        }
        // if no need to copy, returning the same block
        return ptr;
    }

    // If we need more space:
    uint32_t csize = GET_SIZE(HDRP(ptr));
    void *next_bp = NEXT_BLKP(ptr);
    // uint32_t needed = asize - csize; not used

    // Check if next block is free and can be coalesced to meet the new size
    if (!GET_ALLOC(HDRP(next_bp)) && GET_SIZE(HDRP(next_bp)) + csize >= asize) {
        // coalesce with the next block and avoid a full malloc/free
        remove_free_block(next_bp);
        uint32_t new_size = csize + GET_SIZE(HDRP(next_bp));
        PUT(HDRP(ptr), PACK(new_size,1));
        PUT(FTRP(ptr), PACK(new_size,1));

        // If after coalescing we have more space than needed, split the block
        if ((new_size - asize) >= MINBLOCKSIZE) {
            PUT(HDRP(ptr), PACK(asize,1));
            PUT(FTRP(ptr), PACK(asize,1));
            void *new_bp = NEXT_BLKP(ptr);
            PUT(HDRP(new_bp), PACK(new_size - asize,0));
            PUT(FTRP(new_bp), PACK(new_size - asize,0));
            insert_free_block(new_bp, new_size - asize);
        }
        
        // we don't need to copy old data into itself. It's already there.
        return ptr;
    }

    // If we cannot coalesce in place, fallback to the original method:
    void *new_ptr = mm_malloc(size);
    if (new_ptr == NULL)
        return NULL;

    uint32_t copy_size = (size < old_size) ? size : old_size;
    memcpy(new_ptr, ptr, copy_size);
    mm_free(ptr);
    return new_ptr;
}


/*
 * Red-Black Tree (RBT) routines
 */

static void left_rotate(void *x) {
    void *y = RIGHT(x);
    RIGHT(x) = LEFT(y);
    if (LEFT(y) != NIL) PARENT(LEFT(y)) = x;
    PARENT(y) = PARENT(x);
    if (PARENT(x) == NIL) {
        root = y;
    } else if (x == LEFT(PARENT(x))) {
        LEFT(PARENT(x)) = y;
    } else {
        RIGHT(PARENT(x)) = y;
    }
    LEFT(y) = x;
    PARENT(x) = y;
}

static void right_rotate(void *x) {
    void *y = LEFT(x);
    LEFT(x) = RIGHT(y);
    if (RIGHT(y) != NIL) PARENT(RIGHT(y)) = x;
    PARENT(y) = PARENT(x);
    if (PARENT(x) == NIL) {
        root = y;
    } else if (x == RIGHT(PARENT(x))) {
        RIGHT(PARENT(x)) = y;
    } else {
        LEFT(PARENT(x)) = y;
    }
    RIGHT(y) = x;
    PARENT(x) = y;
}

static void rbt_insert(void *bp) {
    void *y = NIL;
    void *x = root;
    uint32_t size = GET_SIZE(HDRP(bp));

    while (x != NIL) {
        y = x;
        uint32_t x_size = GET_SIZE(HDRP(x));
        if (size < x_size)
            x = LEFT(x);
        else
            x = RIGHT(x);
    }

    PARENT(bp) = y;
    if (y == NIL) {
        root = bp;
    } else {
        uint32_t y_size = GET_SIZE(HDRP(y));
        if (size < y_size)
            LEFT(y) = bp;
        else
            RIGHT(y) = bp;
    }

    SET_COLOR(bp, RED);
    rbt_insert_fixup(bp);
}

static void rbt_insert_fixup(void *bp) {
    while (bp != root && COLOR(PARENT(bp)) == RED) {
        if (PARENT(bp) == LEFT(PARENT(PARENT(bp)))) {
            void *uncle = RIGHT(PARENT(PARENT(bp)));
            if (COLOR(uncle) == RED) {
                SET_COLOR(PARENT(bp), BLACK);
                SET_COLOR(uncle, BLACK);
                SET_COLOR(PARENT(PARENT(bp)), RED);
                bp = PARENT(PARENT(bp));
            } else {
                if (bp == RIGHT(PARENT(bp))) {
                    bp = PARENT(bp);
                    left_rotate(bp);
                }
                SET_COLOR(PARENT(bp), BLACK);
                SET_COLOR(PARENT(PARENT(bp)), RED);
                right_rotate(PARENT(PARENT(bp)));
            }
        } else {
            void *uncle = LEFT(PARENT(PARENT(bp)));
            if (COLOR(uncle) == RED) {
                SET_COLOR(PARENT(bp), BLACK);
                SET_COLOR(uncle, BLACK);
                SET_COLOR(PARENT(PARENT(bp)), RED);
                bp = PARENT(PARENT(bp));
            } else {
                if (bp == LEFT(PARENT(bp))) {
                    bp = PARENT(bp);
                    right_rotate(bp);
                }
                SET_COLOR(PARENT(bp), BLACK);
                SET_COLOR(PARENT(PARENT(bp)), RED);
                left_rotate(PARENT(PARENT(bp)));
            }
        }
    }
    SET_COLOR(root, BLACK);
}

static void rbt_transplant(void *u, void *v) {
    if (PARENT(u) == NIL) {
        root = v;
    } else if (u == LEFT(PARENT(u))) {
        LEFT(PARENT(u)) = v;
    } else {
        RIGHT(PARENT(u)) = v;
    }
    PARENT(v) = PARENT(u);
}

static void rbt_remove(void *bp) {
    void *y = bp;
    int y_original_color = COLOR(y);
    void *x;

    if (LEFT(bp) == NIL) {
        x = RIGHT(bp);
        rbt_transplant(bp, RIGHT(bp));
    } else if (RIGHT(bp) == NIL) {
        x = LEFT(bp);
        rbt_transplant(bp, LEFT(bp));
    } else {
        void *m = rbt_minimum(RIGHT(bp));
        y = m;
        y_original_color = COLOR(y);
        x = RIGHT(y);
        if (PARENT(y) == bp) {
            PARENT(x) = y;
        } else {
            rbt_transplant(y, RIGHT(y));
            RIGHT(y) = RIGHT(bp);
            PARENT(RIGHT(y)) = y;
        }
        rbt_transplant(bp, y);
        LEFT(y) = LEFT(bp);
        PARENT(LEFT(y)) = y;
        SET_COLOR(y, COLOR(bp));
    }

    if (y_original_color == BLACK)
        rbt_remove_fixup(x);
}

static void rbt_remove_fixup(void *x) {
    while (x != root && COLOR(x) == BLACK) {
        if (x == LEFT(PARENT(x))) {
            void *w = RIGHT(PARENT(x));
            if (COLOR(w) == RED) {
                SET_COLOR(w, BLACK);
                SET_COLOR(PARENT(x), RED);
                left_rotate(PARENT(x));
                w = RIGHT(PARENT(x));
            }
            if (COLOR(LEFT(w)) == BLACK && COLOR(RIGHT(w)) == BLACK) {
                SET_COLOR(w, RED);
                x = PARENT(x);
            } else {
                if (COLOR(RIGHT(w)) == BLACK) {
                    SET_COLOR(LEFT(w), BLACK);
                    SET_COLOR(w, RED);
                    right_rotate(w);
                    w = RIGHT(PARENT(x));
                }
                SET_COLOR(w, COLOR(PARENT(x)));
                SET_COLOR(PARENT(x), BLACK);
                SET_COLOR(RIGHT(w), BLACK);
                left_rotate(PARENT(x));
                x = root;
            }
        } else {
            void *w = LEFT(PARENT(x));
            if (COLOR(w) == RED) {
                SET_COLOR(w, BLACK);
                SET_COLOR(PARENT(x), RED);
                right_rotate(PARENT(x));
                w = LEFT(PARENT(x));
            }
            if (COLOR(RIGHT(w)) == BLACK && COLOR(LEFT(w)) == BLACK) {
                SET_COLOR(w, RED);
                x = PARENT(x);
            } else {
                if (COLOR(LEFT(w)) == BLACK) {
                    SET_COLOR(RIGHT(w), BLACK);
                    SET_COLOR(w, RED);
                    left_rotate(w);
                    w = LEFT(PARENT(x));
                }
                SET_COLOR(w, COLOR(PARENT(x)));
                SET_COLOR(PARENT(x), BLACK);
                SET_COLOR(LEFT(w), BLACK);
                right_rotate(PARENT(x));
                x = root;
            }
        }
    }
    SET_COLOR(x, BLACK);
}

static void *rbt_minimum(void *node) {
    while (LEFT(node) != NIL)
        node = LEFT(node);
    return node;
}

static void *rbt_find_best_fit(void *node, uint32_t asize, void **best_fit) {
    if (node == NIL) return *best_fit;
    uint32_t nsize = GET_SIZE(HDRP(node));
    if (nsize >= asize) {
        if (*best_fit == NULL || nsize < GET_SIZE(HDRP(*best_fit))) {
            *best_fit = node;
        }
        rbt_find_best_fit(LEFT(node), asize, best_fit);
    } else {
        rbt_find_best_fit(RIGHT(node), asize, best_fit);
    }
    return *best_fit;
}
