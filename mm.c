/****************************************************************************
 * MallocLab for CS:APP 3e                                                  *
 * Student ID: 16307110064                                                  *
 * @author Wang, Chen                                                       *
 * @date December, 14th, 2018                                               *
 *                                                                          *
 *                                                                          *
 * @brief Sophisticated, 32-bit and 64-bit clean allocator based on         *
 * segregated free lists and boundary tag coalescing, modified based on the *
 * code described in the CS:APP3e text. Blocks must be aligned to double    *
 * word (8 byte) boundaries. Minimum block size is 24 bytes.                *
 *                                                                          *
 * @details This implementation adapts various data structures to complete  *
 * the task from different perspectives. In general, a Binary Search Tree is*
 * adapted to speed up the speed of looking for a vacant block in memory.   *
 * Besides, two facilitating lists are also adapted so that the small blocks*
 * can be inserted directly into the list, saving the time of searching in  *
 * the binary search tree.                                                  *
 * Therefore, the global variables clearly displays this point.             *
 * In addition to the @var heap_list_p variable defined by the textbook,    *
 * there are the other global variables indicating the root of the binary   *
 * search tree, the address of the 8 byte list, and the address of the 16   *
 * byte list.                                                               *
 ***************************************************************************/

#include <stdio.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"



/**** The headers defined on lab release and should NOT be changed ******/
/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
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
/***************************  END  *****************************************/




/**************** Basic constants provided by text book *********************/
#define WSIZE       4      /* Word and header/footer size (bytes) */
#define DSIZE       8      /* Double word size (bytes) */
#define CHUNKSIZE  (1<<8)  /* Extend heap by this amount (bytes), [modified from 1<<12 to 1<<8] */
/***************************  END  *****************************************/




/******************** Constants of my own definition ************************/
//Header and footer sign, 8 bytes
#define HEADER_FOOTER 8
//Minimum block size
#define MIN_BLOCK_SIZE 24
/***************************  END  *****************************************/




/**************** Basic macros provided by text book *********************/
#define MAX(x, y)           ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)   ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)         (GET(p) & (~0x7))
#define GET_ALLOC(p)        (GET(p) & (0x1))

/* Given block ptr bp, compute address of its header and footer */
/* Removed unnecessary casting.*/
#define HDRP(bp)            (bp - WSIZE)
#define FTRP(bp)            (bp + GET_SIZE(HDRP(bp)) - DSIZE)
/***************************  END  *****************************************/




/****************** Macros of my own definition ***************************/
/* Get the 64 bit pointer of the address stored in the address p */
#define GET_PTR(p)              (void *)(GET(p)|0x800000000)
#define PTR2INT(p)              (unsigned int)(long)p

/* Determine whether the previous block is allocated and free from header */
#define PREV_ALLOC(header_ptr)  (GET(header_ptr) & (0x2))
#define PREV_FREE(header_ptr)   (GET(header_ptr) & (0x4))

#define SET_PREV_ALLOC(bp)      (GET(HDRP(bp)) |= 0x2)
#define RESET_PREV_ALLOC(bp)    (GET(HDRP(bp)) &= ~0x2)
#define SET_PREV_FREE(bp)       (GET(HDRP(bp)) |= 0x4)
#define RESET_PREV_FREE(bp)     (GET(HDRP(bp)) &= ~0x4)

/*Given pointer p at the second word of the data structure, compute addresses
of its RIGHT,PARENT and SIBLING pointer, left is itself */
#define RIGHT(p)                (p + WSIZE)
#define PARENT(p)               (p + 2 * WSIZE)
#define SIBLING(p)              (p + 3 * WSIZE)

/*Given block pointer bp, get the POINTER of its directions*/
#define GET_PREV(bp)            (PREV_FREE(HDRP(bp)) ? (bp - DSIZE): (bp - GET_SIZE(bp - DSIZE)) )
#define GET_NEXT(bp)            (bp + GET_SIZE(bp - WSIZE))
/***************************  END  *****************************************/




/**** Basic static functions provided by text book (in mm-textbook.c)*******/
/********** Function prototypes for internal helper routines ***************/
static void *extend_heap(size_t size);

static void place(void *bp, size_t a_size);

static void *find_fit(size_t a_size);

static void *coalesce(void *bp);
/***************************  END  ****************************************/




/************ Static functions of my own definition ************************/
/****Self defined function prototypes for internal helper routines *******/
static inline int is_prev_free(void *bp);

static void insert_node(void *bp);

static void delete_node(void *bp);

static void print_block(void *bp);

static void check_tree(void *node);

static void check_list_8(void *bp);

static void check_list_16(void *bp);
/***************************  END  *****************************************/




/*** Basic global variables provided by text book (in mm-textbook.c)*******/
static char *heap_list_p;/* Pointer to first block */
/***************************  END  ****************************************/




/************* Global variables of my own definition ************************/
static void *root;//root of the BST
static void *list_16;//head of the 16-byte list
static void *list_8;//head of the 8-byte list
static void *HEAP_NIL = (void *) 0x800000000;//virtual NULL pointer (0x800000000)
/***************************  END  ****************************************/





/********************  CORE FUNCTION  ***************************************
 **The declaration of this function is defined in mm.h and cannot be changed*
 *                                                                          *
 * mm_init - Initialize the memory manager                                  *
 ***************************************************************************/
int mm_init(void) {
    /* create the initial empty heap */
    if ((heap_list_p = mem_sbrk(6 * WSIZE)) == (void *) -1) return -1;
    PUT(heap_list_p + (2 * WSIZE), 0);              /* Alignment padding */
    PUT(heap_list_p + (3 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_list_p + (4 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_list_p + (5 * WSIZE), PACK(0, 3));     /* Epilogue header */
    heap_list_p += (4 * WSIZE);
    /*init the global variables*/
    root = HEAP_NIL;
    list_16 = HEAP_NIL;
    list_8 = HEAP_NIL;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(MIN_BLOCK_SIZE) == 0) return -1;
    return 0;
}


/********************  CORE FUNCTION  ***************************************
 **The declaration of this function is defined in mm.h and cannot be changed*
 *                                                                          *
 * malloc - Allocate a block with at least size bytes of payload            *
 * When the initialization process is done, the application can use malloc  *
 * method to get a allocated block. The size of the block should be the     *
 * multiple of the alignment. The general implementation idea of this method*
 * is the same as the one on the textbook and this version of implementation*
 * have such functions described as below. The variation from the textbook  *
 * version is the searching for free list method that I have to operate on  *
 * a binary search tree.                                                    *
 *  a) Ignore spurious requests;                                            *
 *  b) Adjust block size to include overhead and alignment requirements;    *
 *  c) Search the free list for a fit;                                      *
 *  d) If no fit found. Get more memory and place the block.                *
 *  e) Place the block into the returned fit place                          *
 ***************************************************************************/
void *malloc(size_t size) {
    char *bp;
    /* Ignore spurious requests */
    if (size <= 0) return 0;

    /* Adjust block size to include overhead and alignment requirements. */
    size_t a_size = ((size + WSIZE) + (DSIZE - 1)) & ~0x7; /* adjusted block size */

    /* Search the free list for a fit */
    if ((bp = find_fit(a_size)) == HEAP_NIL) {
        /* No fit found. Get more memory and place the block */
        extend_heap(a_size);
        bp = find_fit(a_size);
    }
    place(bp, a_size);
    return bp;
}

/********************  CORE FUNCTION  ***************************************
 **The declaration of this function is defined in mm.h and cannot be changed*
 * free - Free a block                                                      *
 * This method returns without modifying block content in two cases:        *
 * a) The block pointer is @code NULL @endcode;                             *
 * b) The block pointer is not @code NULL @endcode but the ALLOCATED tag in *
 * the head part of the block is 0 indicating that this block is not        *
 * allocated. After returning on these abnormal conditions, the free        *
 * function writes the flag symbol on both the head and the foot of the     *
 * block.                                                                   *
 * Finally, this method calls the @code coalesce @endcode methods which     *
 * coalesces the currently freed block with its adjacent blocks and insert  *
 * the newly coalesced block into the binary search tree.                   *
 ***************************************************************************/
void free(void *bp) {
    if (bp == 0) return;
    void *header_ptr = HDRP(bp);
    if (GET_ALLOC(header_ptr) == 0) return;
    int size = GET_SIZE(header_ptr);
    int sign = is_prev_free(bp);
    PUT(header_ptr, PACK(size, sign));
    PUT(FTRP(bp), PACK(size, sign));
    insert_node(coalesce(bp));
}

/********************  CORE FUNCTION  ***************************************
 **The declaration of this function is defined in mm.h and cannot be changed*
 * realloc - Change the size of the block by mallocing a new block, copying *
 *      its data, and freeing the old block(basic idea of naive             *
 *      implementation).                                                    *
 * In this version of implementation, it behaves according to the following *
 * criteria:                                                                *
 * 1) When a @code NULL @endcode pointer is transferred into this method,   *
 *    it does nothing more than the malloc method.                          *
 * 2) When the size of the new required block is zero, it just frees the    *
 *    original block.                                                       *
 * 3) If the new block size is equal to or less than the old block size,    *
 *    it modifies the old block to contain the new size                     *
 * 4) If the new block size is greater than the old block size and the next *
 *    is free, it coalesces the two block into one block and put the new    *
 *    size into the newly generated block.                                  *
 ***************************************************************************/
void *realloc(void *ptr, size_t size) {
    /* If old ptr is NULL, then this is just malloc. */
    if (ptr == 0) return mm_malloc(size);

    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0) {
        mm_free(ptr);
        return 0;
    }


    /* Adjust block size to include overhead and alignment requirements. */
    unsigned int new_size = (unsigned int) (((size + WSIZE) + (DSIZE - 1)) & ~0x7);
    void *header_ptr = HDRP(ptr);
    unsigned int old_size = GET_SIZE(header_ptr);
    void *next = GET_NEXT(ptr);
    void *next_header_ptr = HDRP(next);/* new size is less than/equal to old size */
    unsigned int next_alloc = GET_ALLOC(next_header_ptr);
    unsigned int compound_size = old_size + GET_SIZE(next_header_ptr);
    int new_free_size = !next_alloc ? (compound_size - new_size) : (old_size - new_size);
    if (new_free_size >= HEADER_FOOTER) {
        if (!next_alloc) delete_node(next);
        PUT(header_ptr, PACK(new_size, 1 | is_prev_free(ptr)));
        void *new_next = GET_NEXT(ptr);
        PUT(HDRP(new_next), PACK(new_free_size, 2));
        PUT(FTRP(new_next), PACK(new_free_size, 2));
        insert_node(coalesce(new_next));
        return ptr;
    }
    if (!next_alloc && (compound_size >= new_size)) {
        delete_node(next);
        PUT(header_ptr, PACK(compound_size, 1 | is_prev_free(ptr)));
        SET_PREV_ALLOC(next);
        return ptr;
    }
    // The next block is allocated or the sum of the size of the two blocks is less than new size
    // OK no more way to optimize, I can only find the fit one from the list
    void *new_ptr;
    if ((new_ptr = find_fit(new_size)) == HEAP_NIL) {
        extend_heap(new_size);
        new_ptr = find_fit(new_size);
    }
    place(new_ptr, new_size);
    /*copy content from memory*/
    memcpy(new_ptr, ptr, old_size - WSIZE);
    mm_free(ptr);
    return new_ptr;
}

/********************  CORE FUNCTION  ***************************************
 **The declaration of this function is defined in mm.h and cannot be changed*
 * calloc - Allocate the block and set it to zero.                          *
 * This function will not be tested and this implementation is basic.       *
 ***************************************************************************/
void *calloc(size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr = malloc(bytes);
    memset(newptr, 0, bytes);
    return newptr;
}

/******  END of the main parts of the core functions,**********************/
/**************************************************************************/
/************* below are facilitating static functions ********************/



/****************************************************************************
 * @brief This inline method is a simple method that tests whether the      *
 * previous block of the given block pointer is free.                       *
 ***************************************************************************/
static inline int is_prev_free(void *bp) {
    void *header_ptr = HDRP(bp);
    return PREV_ALLOC(header_ptr) | PREV_FREE(header_ptr);
}


/****************************************************************************
 * @brief extend_heap - Extend heap with free block and return its block    *
 * pointer                                                                  *
 * @details                                                                 *
 * This method is called under two circumstances:                           *
 * when the heap is initialized and when a find_fit method cannot find a    *
 * block with required size.                                                *
 * Before making the system call to increase the heap size, this method     *
 * first checks whether the last block is free. If last block is free, then *
 * it subtracts the size of the free block from the required extension size.*
 * This can maximize the space utilization.                                 *
 * It should be noted that if the last block is not allocated, then after   *
 * the process of extending heap, the last block and the newly generated    *
 * block should be coalesced.                                               *
 ***************************************************************************/
static void *extend_heap(size_t size_) {
    char *bp;
    void *end = mem_heap_hi() - 3;

    int size = (int) size_;
    int is_end_alloc = PREV_ALLOC(end);
    if (!is_end_alloc) {
        if (PREV_FREE(end)) size -= DSIZE;
        else size -= GET_SIZE(end - 4);
    }

    size = MAX(CHUNKSIZE, size);
    bp = mem_sbrk(size);

    /* Initialize free block header/footer and the epilogue header */
    int sign = 0 | is_prev_free(bp);
    PUT(HDRP(bp), PACK(size, sign));     /* Free block header */
    PUT(FTRP(bp), PACK(size, sign));     /* Free block footer */
    PUT(HDRP(GET_NEXT(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    if (!is_end_alloc) bp = coalesce(bp);
    insert_node(bp);
    return bp;
}


/****************************************************************************
 * @brief coalesce - Boundary tag coalescing. Return ptr to coalesced block *
 * @details The implementation of this method is adhere to the guideline of *
 * the textbook. There are totally four cases when a block transferred into *
 * the method. The first case is both its previous block and its next block *
 * are allocated, the second case is its previous block is allocated but    *
 * its next block is not allocated, the third case is its previous block is *
 * not allocated but its next block is allocated, and the last case is      *
 * neither its previous block nor its next block is allocated.              *
 ***************************************************************************/
static void *coalesce(void *bp) {
    void *header_ptr = HDRP(bp);
    void *next = GET_NEXT(bp);
    void *next_header_ptr = HDRP(next);

    size_t size = GET_SIZE(header_ptr);
    size_t prev_alloc = PREV_ALLOC(header_ptr);
    size_t next_alloc = GET_ALLOC(next_header_ptr);

    if (prev_alloc && next_alloc) {             /* Case 1 */
        return bp;
    } else if (prev_alloc) {                    /* Case 2 */
        size += GET_SIZE(next_header_ptr);
        delete_node(GET_NEXT(bp));
        int sign = 0 | is_prev_free(bp);
        PUT(header_ptr, PACK(size, sign));
        PUT(FTRP(bp), PACK(size, sign));
        return bp;
    } else if (next_alloc) {                    /* Case 3 */
        void *prev = GET_PREV(bp);
        int sign = 0 | is_prev_free(prev);
        delete_node(prev);
        size += GET_SIZE(HDRP(prev));
        PUT(HDRP(prev), PACK(size, sign));
        PUT(FTRP(prev), PACK(size, sign));
        return prev;
    } else {                                    /* Case 4 */
        void *prev = GET_PREV(bp);
        void *prev_header_ptr = HDRP(prev);
        size += GET_SIZE(prev_header_ptr) + GET_SIZE(next_header_ptr);
        delete_node(prev);
        delete_node(next);
        int sign = 0 | is_prev_free(bp);
        PUT(prev_header_ptr, PACK(size, sign));
        PUT(FTRP(prev), PACK(size, sign));
        return prev;
    }
}


/****************************************************************************
 * @brief place - Place block of a_size bytes at start of free block bp and *
 * split if remainder would be at least minimum block size.                 *
 * @details This method places the requested block into memory.             *
 * If the remaining space after inserting the current block is greater than *
 * or equal to the size required by the header plus the footer, then a new  *
 * block will occupy the remaining new space. Otherwise, the newly inserted *
 * block will occupy the entire space.                                      *
 ***************************************************************************/
static void place(void *bp, size_t a_size) {
    unsigned int block_size = GET_SIZE(HDRP(bp));
    size_t remaining_size = block_size - a_size;
    int pre_free = 1 | is_prev_free(bp);
    delete_node(bp);
    if ((remaining_size) >= HEADER_FOOTER) {
        PUT(HDRP(bp), PACK(a_size, pre_free));
        bp = GET_NEXT(bp);
        PUT(HDRP(bp), PACK(remaining_size, 2));
        PUT(FTRP(bp), PACK(remaining_size, 2));
        insert_node(coalesce(bp));
    } else
        PUT(HDRP(bp), PACK(block_size, pre_free));
}


/****************************************************************************
 * @brief find_fit - Find a fit for a block with a_size bytes               *
 * @details This implementation of find fit adopts a best fit strategy      *
 * Before traversing the binary search tree. Two other small lists are      *
 * maintained for saving the time of searching for small size blocks.       *
 * The first list contains all the blocks with a size of 8 bytes. Note that *
 * due to the restriction of alignment and the header and footer overhead,  *
 * the minimal block size if 8 bytes.                                       *
 * The second list contains all the blocks with a size between 8 and 16     *
 * bytes.                                                                   *
 * The two lists above all adapts a segregated list style.                  *
 * When searching along the tree, it enters the tree from the root, records *
 * the fitting block and compares the size of the required space and the    *
 * size of the current node in the tree. The tree follows the convention of *
 * the  normal BST that the left child of a node is less than the current   *
 * node and the right child of a node is greater than the current node.     *
 * When completing searching, the @var fit will record the block with the   *
 * least size but can hold the required block.                              *
 * @note It should be noted that the two short lists might have not been    *
 * initialized. In such case, the search in the BST is performed.           *
 * @return The small list if the required size is small and the selected    *
 * list is initialized; the block most close to but greater than the size   *
 * required; the blank node if the required size is greater than the block  *
 * with the greatest size in the binary search tree.                        *
 ***************************************************************************/
static void *find_fit(size_t a_size) {
    if (a_size == 8 && list_8 != HEAP_NIL) return list_8;
    if (a_size <= 16 && list_16 != HEAP_NIL) return list_16;
    /* the most fit block */
    void *fit = HEAP_NIL;
    /* The currently searching node pointer */
    void *searching = root;
    /* Search from the root of the tree to the bottom */
    while (searching != HEAP_NIL)
        /*Record the currently */
        if (a_size <= GET_SIZE(HDRP(searching))) {
            fit = searching;
            searching = GET_PTR(searching);
        } else
            searching = GET_PTR(RIGHT(searching));
    return fit;
}


/****************************************************************************
 * @brief insert_node: Inserts the new block into the linking system        *
 * @details If the size of the node is 8 or 16, then the block will be      *
 * linked to other nodes with the same size in a way behaving like the      *
 * explicit linking list. The root of the link list, aka the root, are two  *
 * global variables. The priority of the two small lists is higher than the *
 * binary search tree. That is, the small blocks will not go into the system*
 * of the binary search tree. If the size of the block is greater than 16,  *
 * then this method will search the binary search tree for a fitting place. *
 * The while loop will continue finding until it finds a place that can     *
 * exactly hold the required block or the @var current_node reaches the end.*
 * It maintains the  other pointers when a node is to be inserted into the  *
 * tree.                                                                    *
 * @note It should be noted that in this version of implementation, multiple*
 * nodes with the same size is allowed. The nodes with the same size simply *
 * become siblings with each other.                                         *
 ***************************************************************************/
static void insert_node(void *bp) {
    RESET_PREV_ALLOC(GET_NEXT(bp));
    void *header_ptr = HDRP(bp);
    size_t block_size = GET_SIZE(header_ptr);
    if (block_size == 8) {
        SET_PREV_FREE(GET_NEXT(bp));
        PUT(bp, PTR2INT(list_8));
        list_8 = bp;
        return;
    }
    if (block_size == 16) {
        //if the block size = 16; insert it to the head of the 16-byte list
        PUT(bp, 0);
        PUT(RIGHT(bp), PTR2INT(list_16));
        PUT(list_16, PTR2INT(bp));
        list_16 = bp;
        return;
    }
    void *parent = HEAP_NIL;
    void *current_node = root;
    int direction = -1;
    /* loop to locate the position */
    while (1) {
        if (current_node == HEAP_NIL) {
            PUT(bp, 0);
            PUT(RIGHT(bp), 0);
            PUT(PARENT(bp), PTR2INT(parent));
            PUT(SIBLING(bp), 0);
            break;
        }
        void *curr_header_ptr = HDRP(current_node);
        /* Case 1: size of the block exactly matches the node. */
        if (GET_SIZE(header_ptr) == GET_SIZE(curr_header_ptr)) {
            PUT(bp, GET(current_node));
            PUT(RIGHT(bp), GET(RIGHT(current_node)));
            PUT(PARENT(GET_PTR(current_node)), PTR2INT(bp));
            PUT(PARENT(GET_PTR(RIGHT(current_node))), PTR2INT(bp));
            PUT(PARENT(bp), PTR2INT(parent));
            PUT(SIBLING(bp), PTR2INT(current_node));
            PUT(current_node, PTR2INT(bp));
            break;
        }
            /* Case 2: size of the block is less than that of the node. */
        else if (GET_SIZE(header_ptr) < GET_SIZE(curr_header_ptr)) {
            parent = current_node;
            direction = 0;
            current_node = GET_PTR(current_node);
        }
            /* Case 3 size of the block is greater than that of the node. */
        else {
            parent = current_node;
            direction = 1;
            current_node = GET_PTR(RIGHT(current_node));
        }
    }
    if (direction == -1) root = bp;
    else if (direction == 0) PUT(parent, PTR2INT(bp));
    else
        PUT(RIGHT(parent), PTR2INT(bp));
}


/****************************************************************************
 * @brief delete_node Removes the node from the link list, maintains the    *
 * link to this node from other nodes.                                      *
 * @details If the block size is 8 bytes, then it maintains the link list of*
 * 8 bytes.
 * The method iterates through the list searching for the global variable,  *
 * the entry of the list, then it removes this block from the list. The time*
 * complexity of this operation is O(n). If the block size is 16 bytes, then*
 * it maintains the link list of 16 bytes. The method fixes the left block  *
 * and the right block removing block. The time complexity of this operation*
 * is O(1). If it is not the cases above, then the block is in the tree.    *
 * If the removing node has a sibling, then the sibling takes the place of  *
 * removing node, taking over the pointers to parent and children. If the   *
 * removing node has no sibling and has only one or no child, then handling *
 * is simple as well. The relationship pointers can be maintained in a      *
 * couple of lines of codes. The trickiest case is when the node has no     *
 * sibling, and when it has both children. In this case, we wont delete the *
 * required node directly but rather let its successor take its place and   *
 * remove the place of its successor. Because the successor of an internal  *
 * node is sure to be a leaf node. Then removing the place of its successor *
 * is simpler.                                                              *
 ***************************************************************************/
static void delete_node(void *bp) {
    SET_PREV_ALLOC(GET_NEXT(bp));
    int block_size = GET_SIZE(HDRP(bp));
    if (block_size == 8) {
        RESET_PREV_FREE(GET_NEXT(bp));
        void *current_block = list_8;
        if (current_block == bp) {
            list_8 = GET_PTR(bp);
            return;
        }
        while (current_block != HEAP_NIL) {
            if (GET_PTR(current_block) == bp) break;
            current_block = GET_PTR(current_block);
        }
        PUT(current_block, PTR2INT(GET_PTR(bp)));
        return;
    }
    if (block_size == 16) {
        void *left_block = GET_PTR(bp);
        void *right_block = GET_PTR(RIGHT(bp));
        if (bp == list_16) list_16 = right_block;
        PUT(RIGHT(left_block), PTR2INT(right_block));
        PUT(right_block, PTR2INT(left_block));
        return;
    }
    /* If the removing node has siblings, the handling is simple */
    if (GET(bp) != 0 && GET_PTR(SIBLING(GET_PTR(bp))) == bp) {
        PUT(SIBLING(GET_PTR(bp)), PTR2INT(GET_PTR(SIBLING(bp))));
        PUT(GET_PTR(SIBLING(bp)), PTR2INT(GET_PTR(bp)));
        return;
    }
        /* If the removing node is the sole node with its size in the
         * binary search tree, the handling is more complex.  * */
    else if (GET(SIBLING(bp)) == 0) {
        if (GET(RIGHT(bp)) != 0) {
            void *successor = GET_PTR(RIGHT(bp));
            while (GET(successor) != 0)
                successor = GET_PTR(successor);
            void *origin_l = GET_PTR(bp);
            void *origin_r = GET_PTR(RIGHT(bp));
            void *successor_r = GET_PTR(RIGHT(successor));
            void *successor_p = GET_PTR(PARENT(successor));
            if (bp != root) {
                void *bpP = GET_PTR(PARENT(bp));
                if (GET_PTR(bpP) == bp)
                    PUT(bpP, PTR2INT(successor));
                else
                    PUT(RIGHT(bpP), PTR2INT(successor));
                PUT(PARENT(successor), PTR2INT(bpP));
            } else {
                root = successor;
                PUT(PARENT(successor), 0);
            }
            PUT(successor, PTR2INT(origin_l));
            PUT(PARENT(origin_l), PTR2INT(successor));
            if (successor != origin_r) {
                PUT(RIGHT(successor), PTR2INT(origin_r));
                PUT(PARENT(origin_r), PTR2INT(successor));
                PUT(successor_p, PTR2INT(successor_r));
                PUT(PARENT(successor_r), PTR2INT(successor_p));
            }
            return;
        }
        if (bp == root) root = GET_PTR(bp);
        if (GET_PTR(GET_PTR(PARENT(bp))) == bp)
            PUT(GET_PTR(PARENT(bp)), PTR2INT(GET_PTR(bp)));
        else
            PUT(RIGHT(GET_PTR(PARENT(bp))), PTR2INT(GET_PTR(bp)));
        PUT(PARENT(GET_PTR(bp)), PTR2INT(GET_PTR(PARENT(bp))));
        return;
    }
    /* Case that the block is first one in the node. */
    void *sibling = GET_PTR(SIBLING(bp));
    if (bp == root) {/* the node is the root */
        root = sibling;
        PUT(PARENT(sibling), 0);
    } else {/* the node is not the root */
        if (GET_PTR(GET_PTR(PARENT(bp))) == bp)
            PUT(GET_PTR(PARENT(bp)), PTR2INT(sibling));
        else
            PUT(RIGHT(GET_PTR(PARENT(bp))), PTR2INT(sibling));
        PUT(PARENT(sibling), PTR2INT(GET_PTR(PARENT(bp))));
    }
    PUT(sibling, GET(bp));
    PUT(RIGHT(sibling), GET(RIGHT(bp)));
    PUT(PARENT(GET_PTR(bp)), PTR2INT(sibling));
    PUT(PARENT(GET_PTR(RIGHT(bp))), PTR2INT(sibling));
}
/******  END of the functions of the memory management part,*************
 ****** below are heap checking function and its auxiliary functions*****/




/********************  CORE FUNCTION  ***************************************
 **The declaration of this function is defined in mm.h and cannot be changed*
 * In order to get more refined control of the heap checking process,       *
 * different level of verbose is used to instruct the method about what info*
 * to display.                                                              *
 * Option 0 indicates that only the check block message are displayed rather*
 *          than the details of the block                                   *
 * Option 1 indicates that the heap block is printed out on the screen      *                                            *
 * Option 2 indicates that the entire Binary Search Tree will be printed in *
 *          a pre-order traversal. In comparision with the traversal of the *
 *          typical binary search tree, the brother nodes will be printed in*
 *          a line.                                                         *
 * Option 3 indicates that the two explicit lists for 8 byte block and 16   *
 *          byte block will be printed. It will not display info about the  *
 *          binary search tree.                                             *
 ***************************************************************************/
void mm_checkheap(int option) {
    char *bp = heap_list_p;

    if (option == 1)
        printf("Heap (%p):\n", (void *) heap_list_p);

    if ((GET_SIZE(heap_list_p) != DSIZE) || !GET_ALLOC(heap_list_p))
        printf("Bad prologue header\n");

    if (option == 1)
        print_block(heap_list_p);
    for (bp = GET_NEXT(bp); GET_SIZE(HDRP(bp)) > 0; bp = GET_NEXT(bp)) {
        if (option == 1) print_block(bp);
        if ((size_t) bp % 8)
            printf("Error: %p is not double word aligned\n", (void *) bp);
    }

    if (option == 1) print_block(bp);
    if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
        printf("Bad epilogue header\n");
    if (option == 2) {
        printf("=============tree=============\n");
        check_tree(root);
    }
    if (option == 3) {
        printf("=========list_8(size = 8)==========\n");
        check_list_8(list_8);
        printf("=========list_16(size = 16)==========\n");
        check_list_16(list_16);
    }
}

/*print the information of a block, including the address, size and allocated bit*/
static void print_block(void *bp) {
    void *header = HDRP(bp);
    int head_size = GET_SIZE(header);
    if (head_size == 0) {
        printf("%p: EOL\n", bp);
        return;
    }
    printf("%p--prev_e_free bit[%d] prev-alloc bit[%d] allocated bit[%d] size[%d]\n",
           bp, PREV_FREE(header) != 0, PREV_ALLOC(header) != 0,
           GET_ALLOC(header), head_size);
}


/*check a free block in the BST
    print the block and check the next node in the list including the brother node
    Then check the left child node and the right child node
*/
static void check_tree(void *node) {
    if (node != HEAP_NIL) {
        print_block(node);
        printf("\tparent:%p;\tbrother:%p;\n\tleft:%p;\tright:%p\n",
               GET_PTR(PARENT(node)), GET_PTR(SIBLING(node)), GET_PTR(node),
               GET_PTR(RIGHT(node)));
        void *temp1 = GET_PTR(SIBLING(node));
        while (temp1 != HEAP_NIL) {
            print_block(temp1);
            printf("\tparent:%p;\tbrother:%p;\n\tleft:%p;\tright:%p\n",
                   GET_PTR(PARENT(temp1)), GET_PTR(SIBLING(temp1)), GET_PTR(temp1),
                   GET_PTR(RIGHT(temp1)));
            temp1 = GET_PTR(SIBLING(temp1));
        }
        check_tree(GET_PTR(node));
        check_tree(GET_PTR(RIGHT(node)));
    }
}

/*check a 16-bit free block in the list_16
    print the block and check the next node in the list
*/
static void check_list_16(void *bp) {
    if (bp != HEAP_NIL) {
        print_block(bp);
        printf("\tleft:%p;\tright:%p\n", GET_PTR(bp), GET_PTR(RIGHT(bp)));
        check_list_16(GET_PTR(RIGHT(bp)));
    }
}

/*check a 16-bit free block in the list_8
    print the block and check the next node in the list
*/
static void check_list_8(void *bp) {
    if (bp != HEAP_NIL) {
        print_block(bp);
        printf("\tleft:%p\n", GET_PTR(bp));
        check_list_8(GET_PTR(bp));
    }
}
