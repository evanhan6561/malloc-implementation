/*
 ******************************************************************************
 *                               mm.c                                         *
 *           64-bit struct-based implicit free list memory allocator          *
 *                      without coalesce functionality                        *
 *                 CSE 361: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                     insert your documentation here. :)                     *
 *                                                                            *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
// #define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);              // word and header size (bytes)
static const size_t dsize = 2 * sizeof(word_t);          // double word size (bytes)
static const size_t min_block_size = 4 * sizeof(word_t); // Minimum block size
static const size_t chunksize = (1 << 12);               // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t prev_alloc_mask = 0x2;
static const word_t size_mask = ~(word_t)0xF;

typedef struct block block_t;
struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    char payload[0];
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
    block_t *next;
    block_t *prev;
};

// Non-circular Doubly Linked List, LIFO
typedef struct FreeList
{
    block_t *root;
} FreeList;

/* Global variables */
/* Pointer to first block */
static block_t *heap_start = NULL;  // Start of heap
static FreeList free_list = {NULL}; // Doubly Linked List of all free_blocks

static void insert_free_block(block_t *block)
{
    if (free_list.root == NULL)
    {
        block->next = NULL;
        block->prev = NULL;
        free_list.root = block;
        return;
    }

    // Non-circular doubly linked insertion
    block->next = free_list.root;
    block->prev = NULL;
    free_list.root->prev = block;

    // The inserted block is now the root
    free_list.root = block;
}

// Removes a specified free block from freelist
static void remove_free_block(block_t *block)
{
    // If only a single node, remove it.
    if (free_list.root == block && free_list.root->prev == free_list.root && free_list.root->next == free_list.root)
    {
        free_list.root = NULL;
        return;
    }

    // If we are removing the root, change the root.
    if (free_list.root == block)
    {
        free_list.root = free_list.root->next;
    }

    block_t *splice_block_next = block->next;
    block_t *splice_block_prev = block->prev;

    if (splice_block_prev != NULL)
    {
        splice_block_prev->next = splice_block_next;
    }
    if (splice_block_next != NULL)
    {
        splice_block_next->prev = splice_block_prev;
    }
}

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool prev_alloc, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool prev_alloc, bool alloc);
static void write_footer(block_t *block, size_t size, bool prev_alloc, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

static void print_heap();
static void print_free_list();

static bool get_prev_alloc(block_t *block);
static void write_prev_alloc_of_next_block(block_t *block, bool prev_alloc);
static void write_prev_alloc(block_t* block, bool prev_alloc);

/*
 * <what does mm_init do?>
 */
bool mm_init(void)
{
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1)
    {
        return false;
    }

    start[0] = pack(0, true, true); // Prologue footer
    start[1] = pack(0, false, true); // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *)&(start[1]);

    // Extend the empty heap and insert it into the freelist
    block_t *first_ever_block = extend_heap(chunksize);
    write_header(first_ever_block, get_size(first_ever_block), true, false);
    write_footer(first_ever_block, get_size(first_ever_block), true, false);

    insert_free_block(first_ever_block);

    if (free_list.root == NULL)
    {
        return false;
    }
    return true;
}

/*
 * <what does mmalloc do?>
 */
void *malloc(size_t size)
{
    dbg_printf("Malloc %lu\n", size);
    dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);  // If we remove footer, +wsize instead of +dsize

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }
        insert_free_block(block);
    }

    place(block, asize);
    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/*
 * <what does free do?>
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }


    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    dbg_printf("Free %p\n", block);

    bool old_prev_alloc = get_prev_alloc(block);
    write_header(block, size, old_prev_alloc, false);
    write_footer(block, size, old_prev_alloc, false);

    block_t *coalesce_ptr = coalesce(block);
    insert_free_block(coalesce_ptr);
}

/*
 * <what does realloc do?>
 */
void *realloc(void *ptr, size_t size)
{
    dbg_printf("Realloc %p\n", ptr);
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * <what does calloc do?>
 */
void *calloc(size_t elements, size_t size)
{
    dbg_printf("Calloc %lu\n", size);
    void *bp;
    size_t asize = elements * size;

    if (asize / elements != size)
    {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * <what does extend_heap do?>
 * Extends the heap by size bytes, which may trigger coalesce().
 * Returns a pointer to the last free block.
 * 
 * Implementation:
 * Always repurposes the dummy epilogue into the header of the last free block
 */
static block_t *extend_heap(size_t size)
{
    dbg_printf("Extend Heap!\n");
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    bool old_prev_alloc = get_prev_alloc(block);
    write_header(block, size, old_prev_alloc, false);
    write_footer(block, size, old_prev_alloc, false);

    write_prev_alloc(block, old_prev_alloc);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, false, true);

    // Coalesce in case the previous block was free
    block_t *coalesce_ptr = coalesce(block);

    // Only remove the block if it's found in the freelist
    if (!old_prev_alloc)
    {
        remove_free_block(coalesce_ptr);
    }

    return coalesce_ptr;
}

/*
 * <what does coalesce do?>
 * Assumes that the passed block is free?
 * Merge with adjacent blocks if they are free
 */
static block_t *coalesce(block_t *block)
{
    // 4 Possible Cases
    size_t current_size = get_size(block);

    // block_t *prev_block = find_prev(block);
    block_t *next_block = find_next(block);

    // Edge cases? Consider at the ends
    bool prev_is_allocated = get_prev_alloc(block);
    bool next_is_allocated = get_alloc(next_block);
    if (block == next_block) {
        dbg_printf("Coalesce at right edge of heap. %p\n", block);
        next_is_allocated = true;
    }


    if (!prev_is_allocated)
    {
        if (block == find_prev(block)) {
        dbg_printf("Coalesce at left edge of heap. %p\n", block);
        prev_is_allocated = true;
        }
    }
    

    if (prev_is_allocated && next_is_allocated)
    {
        // No coalescing required, but add to free_list
        dbg_printf("No Coalesce\n");

        // Copy header to footer
        write_footer(block, get_size(block), get_prev_alloc(block), get_alloc(block));

        // prev-alloc bit
        write_prev_alloc_of_next_block(block, false);
        return block;
    }
    else if (prev_is_allocated && !next_is_allocated)
    {
        // Coalesce with the next block
        dbg_printf("Coalesce with next block\n");
        size_t next_size = get_size(next_block);
        size_t new_size = current_size + next_size;

        // Create/Update header and footer
        bool old_prev_alloc = get_prev_alloc(block);
        write_header(block, new_size, old_prev_alloc, false);
        write_footer(block, new_size, old_prev_alloc, false);

        // Splice out the next block from free_list
        remove_free_block(next_block);

        write_prev_alloc_of_next_block(block, false); // Not necessary?
        return block;
    }
    else if (!prev_is_allocated && next_is_allocated)
    {
        dbg_printf("Coalesce with previous, block: %p\n", block);
        // Coalesce with the previous block
        block_t *prev_block = find_prev(block);
        size_t prev_size = get_size(prev_block);
        size_t new_size = current_size + prev_size;

        dbg_printf("prev-block: %p\n", prev_block);
        // Create/Update header and footer
        bool old_prev_alloc = get_prev_alloc(prev_block);
        write_header(prev_block, new_size, old_prev_alloc, false);
        write_footer(prev_block, new_size, old_prev_alloc, false);

        // Update free_list
        remove_free_block(prev_block);

        write_prev_alloc_of_next_block(prev_block, false);
        return prev_block;
    }
    else
    {
        dbg_printf("Coalesce 3\n");
        // Merge all 3 blocks
        block_t *prev_block = find_prev(block);
        size_t prev_size = get_size(prev_block);
        size_t next_size = get_size(next_block);
        size_t new_size = prev_size + current_size + next_size;

        // Create/Update header and footer
        bool old_prev_alloc = get_prev_alloc(prev_block);
        write_header(prev_block, new_size, old_prev_alloc, false);
        write_footer(prev_block, new_size, old_prev_alloc, false);

        // List Manipulation
        remove_free_block(next_block);
        remove_free_block(prev_block);

        write_prev_alloc_of_next_block(prev_block, false);
        return prev_block;
    }
}

/*
 * <what does place do?>
 * Placing a block into a free block? It assumes that the parameter block is free
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block); // Current Size
    dbg_printf("Place this block: %p, csize: %zu, asize: %zu\n", block, csize, asize);

    if ((csize - asize) >= min_block_size)
    {
        // Splitting a free block into allocated | split
        block_t *block_next;

        // Allocation, remove the free block
        bool old_prev_alloc = get_prev_alloc(block);
        write_header(block, asize, old_prev_alloc, true);
        // write_footer(block, asize, old_prev_alloc, true);
        remove_free_block(block);

        
        // Construct and insert the leftover free block
        block_next = find_next(block);
        write_header(block_next, csize - asize, true, false);
        write_footer(block_next, csize - asize, true, false);

        insert_free_block(block_next);
    }

    else
    {
        // No splitting required. Therefore remove from free list
        remove_free_block(block);

        // Allocation
        bool old_prev_alloc = get_prev_alloc(block);
        write_header(block, csize, old_prev_alloc, true);
        // write_footer(block, csize, old_prev_alloc, true);
        write_prev_alloc_of_next_block(block, true);
    }
}

/*
 * <what does find_fit do?>
 * Finds a free block that can fit asize
 * 
 * Currently, Next-Fit implementation
 */
static block_t *find_fit(size_t asize)
{
    block_t *block = free_list.root;

    while (block != NULL)
    {
        if (!(get_alloc(block)) && (asize <= get_size(block)))
        {
            return block;
        }
        block = block->next;
    }

    return NULL; // no fit found
}

/* 
 * <what does your heap checker do?>
 * Please keep modularity in mind when you're writing the heap checker!
 */
bool mm_checkheap(int line)
{
    // Make sure it is doubly linked.
    block_t *current = free_list.root;
    while (current != NULL)
    {
        if (current->next && current != current->next->prev)
        {
            print_heap();
            printf("Not Doubly Linked Properly, Line: %d\n", line);
            return false;
        }
        current = current->next;
    }

    // Make sure all blocks in the freelist are actually free
    current = free_list.root;
    while (current != NULL)
    {
        if (get_alloc(current))
        {
            print_heap();
            printf("Free List contains an allocated Block, Line: %d\n", line);
            return false;
        }
        current = current->next;
    }

    // All free blocks? No mark system
    int num_free_blocks_in_list = 0; 
    current = free_list.root;
    while (current != NULL) {
        current = current -> next;
        num_free_blocks_in_list++;
    }
    

    // Iterate through heap implicitly
    int num_free_blocks_in_heap = 0;
    block_t *block;
    for (block = heap_start; get_size(block) > 0; block = find_next(block))
    {
        if (!get_alloc(block))
        {
            num_free_blocks_in_heap++;
        }
    }

    if (num_free_blocks_in_heap != num_free_blocks_in_list)
    {
        print_heap();
        print_free_list();
        printf("Mismatch b/n heap and list. Line: %d\n", line);
        printf("Free Blocks in Heap: %d\n", num_free_blocks_in_heap);
        printf("Free Blocks in List: %d\n", num_free_blocks_in_list);
        return false;
    }

    /* Removing footer checks*/
    // Check if prev_alloc is maintained
    for (block = heap_start; get_size(find_next(block)) > 0; block = find_next(block))
    {
        if (get_alloc(block) != get_prev_alloc(find_next(block))) {
            printf("Prev-Alloc bit mismatch.\n");
            print_heap();
            return false;
        }
    }

    // Check if a free block's header == footer
    for (block = heap_start; get_size(block) > 0; block = find_next(block))
    {
        if (!get_alloc(block)) {
            // Only for free blocks
            word_t header = block -> header;
            word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
            word_t footer = *footerp;

            if (header != footer) {
                printf("Footer and Header of free block don't match.\n");
                print_heap();
                return false;
            }
        }
    }

    return true;
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n - 1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool prev_alloc, bool alloc)
{
    return size | (prev_alloc << 1) | alloc;
}

/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - dsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool prev_alloc, bool alloc)
{
    block->header = pack(size, prev_alloc, alloc);
}

/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool prev_alloc, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, prev_alloc, alloc);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}

// Traverse the heap and print it out.
static void print_block(block_t *block)
{
    if (!get_alloc(block))
    {
        printf("[Addr: %p, Size: %lu, PrevAlloc: %u, Alloc: %u| next: %p, prev: %p]\n",
               block, get_size(block), get_prev_alloc(block),get_alloc(block), block->next, block->prev);
    }
    else
    {
        printf("[Addr: %p, Size: %lu, PrevAlloc: %u, Alloc: %u]\n",
               block, get_size(block), get_prev_alloc(block), get_alloc(block));
    }
}
static void print_heap()
{
    printf("HEAP DUMP\n");
    block_t *block;
    for (block = heap_start; get_size(block) > 0; block = find_next(block))
    {
        print_block(block);
    }
}
static void print_free_list()
{
    printf("FREELIST DUMP vvv\n");
    block_t *current = free_list.root;
    while (current != NULL){
        print_block(current);
        current = current->next;
    }
}

// Returns the prev_alloc bit of a block
static bool get_prev_alloc(block_t *block)
{
    return (bool) !!(block->header & prev_alloc_mask);
}

static void write_prev_alloc_of_next_block(block_t *block, bool prev_alloc)
{
    block_t *next_block = find_next(block);
    word_t new_header = pack(get_size(next_block), prev_alloc, get_alloc(next_block));
    next_block->header = new_header;
}

static void write_prev_alloc(block_t* block, bool prev_alloc)
{
    block->header = get_size(block) | (prev_alloc << 1) | get_alloc(block);
}
