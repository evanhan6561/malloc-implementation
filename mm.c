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

#include "stree.h"

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);              // word and header size (bytes)
static const size_t dsize = 2 * sizeof(word_t);          // double word size (bytes)
static const size_t min_block_size = 4 * sizeof(word_t); // Minimum block size
static const size_t chunksize = (1 << 12);               // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t prev_alloc_mask = 0x2;
static const word_t grouped_mask = 0x4;
static const word_t size_mask = ~(word_t)0xF;

// Segregated List Constants
#define NUM_SMALL_BINS 256
#define NUM_LARGE_BINS 256
#define LARGE_BIN_RANGE 64 // The range a large bin covers. The last large_bin contains mega blocks.
static size_t MIN_SMALL_BIN_SIZE;
static size_t MAX_SMALL_BIN_SIZE;
static size_t MIN_LARGE_BIN_SIZE;

// Grouped Block Constants
static const size_t NUM_BLOCKS_IN_GROUP = 64;
static const size_t MAX_GROUPED_SIZE = 128;

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

    /* Megablock Data */
    word_t alloc_vector; // bit vector to track 64 fixed-size blocks
    word_t accepted_size;
    char fixed_payload[0];
};

// Segregated Lists
typedef struct Bins
{
    block_t *small_bins[NUM_SMALL_BINS];
    block_t *large_bins[NUM_LARGE_BINS];
} Bins;

/* Global variables */
static block_t *heap_start = NULL; // Start of heap
static Bins *bins = NULL;          // Pointers to segregated lists
static tree_t *tree = NULL;        // Tree to hold free/partially filled grouped_blocks

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
static void write_prev_alloc(block_t *block, bool prev_alloc);

static void insert_free_block(block_t **list, block_t *block); // Helper function
static void remove_free_block(block_t **list, block_t *block); // Helper function

static bool is_small(size_t size);
static bool is_large(size_t size);
static size_t small_idx(size_t size);
static size_t large_idx(size_t size);
static void small_bin_insert(block_t *block);
static void large_bin_insert(block_t *block);
static void insert_block(block_t *block); // Inserts into a block into some seg list
static void small_bin_remove(block_t *block);
static void large_bin_remove(block_t *block);
static void remove_block(block_t *block);

static void write_grouped(block_t *block, bool grouped);
static bool is_grouped(block_t *block);
static bool is_grouped_size(size_t size);
static bool is_grouped_ptr(void *bp);
static size_t get_group_idx(void *bp);
static void set_alloc_vector_bit(block_t *grouped_block, size_t idx, bool bit);

/*
 * <what does mm_init do?>
 */
bool mm_init(void)
{
    // Initialize Static Global Variables.
    MIN_SMALL_BIN_SIZE = min_block_size;
    MAX_SMALL_BIN_SIZE = MIN_SMALL_BIN_SIZE + (NUM_SMALL_BINS - 1) * dsize;
    MIN_LARGE_BIN_SIZE = MAX_SMALL_BIN_SIZE + dsize;

    // Allocate and zero initialize bins
    bins = (Bins *)mem_sbrk(sizeof(Bins));
    size_t i;
    for (i = 0; i < NUM_SMALL_BINS; i++)
    {
        bins->small_bins[i] = NULL;
    }
    for (i = 0; i < NUM_LARGE_BINS; i++)
    {
        bins->large_bins[i] = NULL;
    }

    // Allocate and initialize tree to hold grouped blocks
    tree = tree_new();
    tree_insert(tree, (long)bins, (void *)bins);
    // printf("No cast: %p, Casted: %lx, Tree Return: %p\n", bins, (long)bins, (Bins *) tree_find(tree, (long)bins));

    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1)
    {
        return false;
    }

    start[0] = pack(0, true, true);  // Prologue footer
    start[1] = pack(0, false, true); // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *)&(start[1]);

    // Extend the empty heap and insert it into the freelist
    block_t *first_ever_block = extend_heap(chunksize);
    if (first_ever_block == NULL)
    {
        return false;
    }

    write_header(first_ever_block, get_size(first_ever_block), true, false);
    write_footer(first_ever_block, get_size(first_ever_block), true, false);

    insert_block(first_ever_block);

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
    asize = round_up(size + wsize, dsize); // If we remove footer, +wsize instead of +dsize
    if (asize < min_block_size)
    {
        asize = min_block_size;
    }
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
        insert_block(block);
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
    // Todo: Check if bp is contained in a grouped block

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    dbg_printf("Free %p\n", block);

    bool old_prev_alloc = get_prev_alloc(block);
    write_header(block, size, old_prev_alloc, false);
    write_footer(block, size, old_prev_alloc, false);

    block_t *coalesce_ptr = coalesce(block);
    insert_block(coalesce_ptr);
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
        remove_block(coalesce_ptr);
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
    if (block == next_block)
    {
        dbg_printf("Coalesce at right edge of heap. %p\n", block);
        next_is_allocated = true;
    }

    if (!prev_is_allocated)
    {
        if (block == find_prev(block))
        {
            dbg_printf("Coalesce at left edge of heap. %p\n", block);
            prev_is_allocated = true;
        }
    }

    if (prev_is_allocated && next_is_allocated)
    {
        // No coalescing required, but add to free_list
        dbg_printf("No Coalesce\n");

        // Copy header to footer and mark next
        write_footer(block, get_size(block), get_prev_alloc(block), get_alloc(block));
        write_prev_alloc_of_next_block(block, false);
        return block;
    }
    else if (prev_is_allocated && !next_is_allocated)
    {
        /* Coalesce with next block */
        // First grab metadata
        dbg_printf("Coalesce with next block\n");
        size_t next_size = get_size(next_block);
        size_t new_size = current_size + next_size;
        bool old_prev_alloc = get_prev_alloc(block);

        // Splice out the next block from free_list
        remove_block(next_block);

        // Create/Update header and footer
        write_header(block, new_size, old_prev_alloc, false);
        write_footer(block, new_size, old_prev_alloc, false);
        write_prev_alloc_of_next_block(block, false); // Not necessary?

        return block;
    }
    else if (!prev_is_allocated && next_is_allocated)
    {
        // Coalesce with the previous block
        block_t *prev_block = find_prev(block);
        size_t prev_size = get_size(prev_block);
        size_t new_size = current_size + prev_size;
        bool old_prev_alloc = get_prev_alloc(prev_block);

        dbg_printf("Coalesce with previous, block: %p. prev-block: %p\n", block, prev_block);

        // Update free_list
        remove_block(prev_block);

        // Create/Update header and footer
        write_header(prev_block, new_size, old_prev_alloc, false);
        write_footer(prev_block, new_size, old_prev_alloc, false);
        write_prev_alloc_of_next_block(prev_block, false);
        return prev_block;
    }
    else
    {
        // Merge all 3 blocks
        dbg_printf("Coalesce 3\n");

        block_t *prev_block = find_prev(block);
        size_t prev_size = get_size(prev_block);
        size_t next_size = get_size(next_block);
        size_t new_size = prev_size + current_size + next_size;
        bool old_prev_alloc = get_prev_alloc(prev_block);

        // List Manipulation
        remove_block(next_block);
        remove_block(prev_block);

        // Create/Update header and footer
        write_header(prev_block, new_size, old_prev_alloc, false);
        write_footer(prev_block, new_size, old_prev_alloc, false);

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
        remove_block(block);
        write_header(block, asize, old_prev_alloc, true);

        // Construct and insert the leftover free block
        block_next = find_next(block);
        write_header(block_next, csize - asize, true, false);
        write_footer(block_next, csize - asize, true, false);

        insert_block(block_next);
    }

    else
    {
        // No splitting required. Therefore remove from free list
        remove_block(block);

        // Allocation
        bool old_prev_alloc = get_prev_alloc(block);
        write_header(block, csize, old_prev_alloc, true);

        write_prev_alloc_of_next_block(block, true);
    }
}

/*
 * <what does find_fit do?>
 * Finds a free block that can fit asize.
 * 
 * Currently, Next-Fit implementation
 */
static block_t *find_fit(size_t asize)
{
    // First look in the bin it'd fit into normally. Then keep moving up a class and searching for a block.
    block_t **list = NULL;
    bool in_small_bin = false;
    if (is_small(asize))
    {
        size_t idx = small_idx(asize);
        list = &bins->small_bins[idx];
        in_small_bin = true;
    }
    else if (is_large(asize))
    {
        size_t idx = large_idx(asize);
        list = &bins->large_bins[idx];
    }
    else
    {
        printf("Block is not large or small!");
    }

    // We've found a list to start searching in. Search it then keep moving up.
    block_t **current_list = list;
    block_t **end = ((bins->small_bins) + NUM_SMALL_BINS + NUM_LARGE_BINS);
    while (current_list != end)
    {
        // Traverse this list. If it's a small bin we don't need to traverse, just check 1 block.
        if (in_small_bin)
        {
            // If we're in the last small_list, switch to traversal mode.
            if (current_list == (bins->large_bins - 1))
            {
                in_small_bin = false;
            }

            block_t *block = *current_list;
            if (block != NULL && !(get_alloc(block)) && (asize <= get_size(block)))
            {
                return block;
            }
        }
        else
        {
            block_t *block = *current_list;
            while (block != NULL)
            {
                if (!(get_alloc(block)) && (asize <= get_size(block)))
                {
                    return block;
                }
                block = block->next;
            }
        }

        current_list++; // Move to the next list
    }

    return NULL; // no fit found
}

/* 
 * <what does your heap checker do?>
 * Please keep modularity in mind when you're writing the heap checker!
 */
bool mm_checkheap(int line)
{
    // Make sure every seg list is doubly linked.
    block_t **current_list = &bins->small_bins[0];
    block_t **end = ((bins->small_bins) + NUM_SMALL_BINS + NUM_LARGE_BINS);
    while (current_list != end)
    {
        // Traverse this list
        block_t *current = *current_list;
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

        current_list++; // Move to the next list
    }

    // Make sure all blocks in the freelist are actually free
    current_list = &bins->small_bins[0];
    end = ((bins->small_bins) + NUM_SMALL_BINS + NUM_LARGE_BINS);
    while (current_list != end)
    {
        // Traverse this list
        block_t *current = *current_list;
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

        current_list++; // Move to the next list
    }

    // Do the list and heap have matching num of blocks? No mark system
    current_list = &bins->small_bins[0];
    end = ((bins->small_bins) + NUM_SMALL_BINS + NUM_LARGE_BINS);
    int num_free_blocks_in_list = 0;
    while (current_list != end)
    {
        // Traverse this list
        block_t *current = *current_list;
        while (current != NULL)
        {
            num_free_blocks_in_list++;
            current = current->next;
        }

        current_list++; // Move to the next list
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
        if (get_alloc(block) != get_prev_alloc(find_next(block)))
        {
            printf("Prev-Alloc bit mismatch.\n");
            print_heap();
            return false;
        }
    }

    // Check if a free block's header == footer
    for (block = heap_start; get_size(block) > 0; block = find_next(block))
    {
        if (!get_alloc(block))
        {
            // Only for free blocks
            word_t header = block->header;
            word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
            word_t footer = *footerp;

            if (header != footer)
            {
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
    return asize - wsize;
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
               block, get_size(block), get_prev_alloc(block), get_alloc(block), block->next, block->prev);
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
    block_t **current_list = bins->small_bins;
    block_t **end = ((bins->small_bins) + NUM_SMALL_BINS + NUM_LARGE_BINS);
    while (current_list != end)
    {
        // Traverse this list
        block_t *current = *current_list;
        while (current != NULL)
        {
            print_block(current);
            current = current->next;
        }

        current_list++; // Move to the next list
    }
}

static void insert_free_block(block_t **list, block_t *block)
{
    if (*list == NULL)
    {
        block->next = NULL;
        block->prev = NULL;
        *list = block;
        return;
    }

    // Non-circular doubly linked insertion
    block->next = *list;
    block->prev = NULL;
    (*list)->prev = block;

    // The inserted block is now the root
    *list = block;
}

// Removes a specified free block from freelist
static void remove_free_block(block_t **list, block_t *block)
{
    // If only a single node, remove it.
    if (*list == block && (*list)->prev == (*list) && (*list)->next == *list)
    {
        *list = NULL;
        return;
    }

    // If we are removing the root, change the root.
    if (*list == block)
    {
        *list = (*list)->next;
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

// Returns the prev_alloc bit of a block
static bool get_prev_alloc(block_t *block)
{
    return (bool)!!(block->header & prev_alloc_mask);
}

static void write_prev_alloc_of_next_block(block_t *block, bool prev_alloc)
{
    block_t *next_block = find_next(block);
    word_t new_header = pack(get_size(next_block), prev_alloc, get_alloc(next_block));
    next_block->header = new_header;
}

static void write_prev_alloc(block_t *block, bool prev_alloc)
{
    block->header = get_size(block) | (prev_alloc << 1) | get_alloc(block);
}

/* Segregated List Helper Functions ---------- */
static bool is_small(size_t size)
{
    return size <= MAX_SMALL_BIN_SIZE;
}

static bool is_large(size_t size)
{
    return !is_small(size);
}

static size_t small_idx(size_t size)
{
    return (size - MIN_SMALL_BIN_SIZE) / dsize;
}

static size_t large_idx(size_t size)
{
    size_t idx = (size - MIN_SMALL_BIN_SIZE) / LARGE_BIN_RANGE;
    if (idx >= NUM_LARGE_BINS)
    {
        return NUM_LARGE_BINS - 1;
    }
    return idx;
}

static void small_bin_insert(block_t *block)
{
    size_t size = get_size(block);
    int small_list_idx = small_idx(size);
    block_t **list_head = &bins->small_bins[small_list_idx];
    insert_free_block(list_head, block);
}

static void large_bin_insert(block_t *block)
{
    size_t size = get_size(block);
    size_t large_list_idx = large_idx(size);
    block_t **list_head = &bins->large_bins[large_list_idx];
    insert_free_block(list_head, block);
}

// Inserts into a block into some seg list
static void insert_block(block_t *block)
{
    size_t size = get_size(block);
    if (is_small(size))
    {
        small_bin_insert(block);
    }
    else if (is_large(size))
    {
        large_bin_insert(block);
    }
    else
    {
        printf("Critical Error! Block is not small or large");
    }
}

static void small_bin_remove(block_t *block)
{
    size_t size = get_size(block);
    int small_list_idx = small_idx(size);
    block_t **list_head = &bins->small_bins[small_list_idx];
    remove_free_block(list_head, block);
}
static void large_bin_remove(block_t *block)
{
    size_t size = get_size(block);
    size_t large_list_idx = large_idx(size);
    block_t **list_head = &bins->large_bins[large_list_idx];
    remove_free_block(list_head, block);
}
static void remove_block(block_t *block)
{
    size_t size = get_size(block);
    if (is_small(size))
    {
        small_bin_remove(block);
    }
    else if (is_large(size))
    {
        large_bin_remove(block);
    }
    else
    {
        printf("Critical Error! Block is not small or large");
    }
}

static void write_grouped(block_t *block, bool grouped)
{
    block->header = get_size(block) | grouped << 2 | get_prev_alloc(block) << 1 | get_alloc(block);
}

static bool is_grouped(block_t *block)
{
    return (bool)!!(block->header & grouped_mask);
}

static bool is_grouped_size(size_t size)
{
    return size <= MAX_GROUPED_SIZE;
}

// When freeing, check if a pointer is found in a grouped block
static bool is_grouped_ptr(void *bp)
{
    block_t **closest_group = (block_t **)tree_find_nearest(tree, (tkey_t)bp);
    word_t ptr = (word_t)bp;
    word_t min_value = (word_t)(*closest_group)->fixed_payload;
    word_t offset = (*closest_group)->accepted_size * (NUM_BLOCKS_IN_GROUP - 1);
    word_t max_value = min_value + offset;

    return min_value <= ptr && ptr <= max_value;
}

// 
static size_t get_group_idx(void *bp)
{
    block_t **closest_group = (block_t **)tree_find_nearest(tree, (tkey_t)bp);
    size_t ptr = (size_t)bp;
    size_t min_value = (size_t)(*closest_group)->fixed_payload;
    size_t group_idx = (ptr - min_value) / (*closest_group)->accepted_size;
    return group_idx;
}

static void set_alloc_vector_bit(block_t *grouped_block, size_t idx, bool bit)
{
    grouped_block->alloc_vector |= (bit << idx);
}

// find_fit is going to traverse the tree and find a grouped block
static void allocate_grouped_block_member(block_t *grouped_block)
{
    // Find the first free bit in grouped_block and then set that to 1.
    word_t inverted_alloc_vector = ~(grouped_block->alloc_vector);
    int idx = __builtin_ffsl(inverted_alloc_vector) - 1;
    set_alloc_vector_bit(grouped_block, idx, true);

    // Remove a grouped block from the free tree if it's full
    if (grouped_block->alloc_vector == (word_t)~0)
    {
        tree_remove(tree, (tkey_t)grouped_block->fixed_payload);
    }
}

// Assuming bp is in a group, it will free something
static void free_grouped_block_member(void *bp)
{
    // Find out which grouped block bp belongs to
    block_t *closest_grouped_block = (block_t *)tree_find_nearest(tree, (tkey_t)bp);

    // Mark the member as free in our bit vector
    size_t idx = get_group_idx(bp);
    set_alloc_vector_bit(closest_grouped_block, idx, false);
}