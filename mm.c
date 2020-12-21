/*
 ******************************************************************************
 *                               mm.c                                         
 *           64-bit struct-based segregated explicit free list memory allocator          
 *                                          
 *                 CSE 361: Introduction to Computer Systems                  
 *                                                                            
 *  ************************************************************************  *
 *      Implementation Details:
 * 
 *      Segregated Explicit Free Lists
 *          Each individual bin is an explicit free list, a list that
 *          holds free blocks.         
 * 
 *          Small Bins hold only a single block size
 * 
 *          Large bins hold power of two ranges.
 *              i.e. The first large bin can hold 1 block size, the 
 *              second large bin can hold 2 block sizes, the third 4...
 * 
 *          The last large bin holds any blocks too large to fit into
 *          any other bin.
 * 
 *      Removed Footer
 *          Allocated Blocks no longer have a footer. The second 
 *          least significant bit of the
 *          header is devoted to a prev-alloc bit which enables this.
 * 
 *      16 Byte Minimum Block Size
 *          Optimization for payloads of size 1-8. Typically, the 
 *          minimum block size is 32 because a free block is composed of
 *          an 8 byte header, 8 byte next pointer, 8 byte prev pointer,
 *          and 8 byte footer.
 *          However, the 3rd least significant bit of the header has
 *          been devoted to an "is size 16" indicator. 
 *          Additionally, the 4th least significant bit of the header
 *          has been devoted to a "previous block is size 16" indicator.
 * 
 *                                                                            
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
#include <math.h> // Import math to use log2l() when calculating large_idx

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
/* When debugging is disabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);              // word and header size (bytes)
static const size_t dsize = 2 * sizeof(word_t);          // double word size (bytes)
static const size_t min_block_size = 2 * sizeof(word_t); // Minimum block size
static const size_t chunksize = (1 << 12);               // requires (chunksize % 16 == 0)

static const word_t prev_alloc_bit_offset = 1;
static const word_t sixteen_bit_offset = 2;
static const word_t prev_sixteen_bit_offset = 3;

static const word_t alloc_mask = 0x1;
static const word_t prev_alloc_mask = 0x2;
static const word_t sixteen_mask = 0x4;
static const word_t prev_sixteen_mask = 0x8;
static const word_t size_mask = ~(word_t)0xF;

#define NUM_SMALL_BINS 240
#define NUM_LARGE_BINS 16

static size_t MIN_SMALL_BIN_SIZE;
static size_t MAX_SMALL_BIN_SIZE;
static size_t MIN_LARGE_BIN_SIZE;

/**
 * @brief The structure of normal blocks. 
 * 
 *          16-byte blocks are the same type but their members are organized differently.
 *          Namely, their header is actually their block_t *next member
 *          And their next ptr is actually their block_t *prev member
 * 
 *          However, a 16-byte block's next member variable also stores metadata in the last 4 bits,
 *          and should only be handled by helper functions designed for 16-byte blocks.
 * 
 *          In summary, the provided helper functions should be used when handling
 *          16-byte blocks.
 */
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

// Segregated Lists, our global list will be the MEGA_BLOCK holder
typedef struct Bins
{
    block_t *small_bins[NUM_SMALL_BINS];
    block_t *large_bins[NUM_LARGE_BINS];
} Bins;

/* Global variables */
static block_t *heap_start = NULL; // Pointer to the very first block
static Bins *bins = NULL;          // Pointers to segregated lists

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);
static void write_coalesce_header(block_t *block, size_t new_size);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool prev_sixteen, bool sixteen, bool prev_alloc, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool prev_sixteen, bool sixteen, bool prev_alloc, bool alloc);
static void write_footer(block_t *block, size_t size, bool prev_sixteen, bool sixteen, bool prev_alloc, bool alloc);
static void write_header_to_footer(block_t *block, size_t size);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

static void print_heap();
static void print_block(block_t *block);
static void print_free_list();

static bool get_prev_alloc(block_t *block);
static void write_prev_alloc_of_next_block(block_t *block, bool prev_alloc);
static void write_prev_alloc(block_t *block, bool prev_alloc);

static void insert_free_block(block_t **list, block_t *block);
static void remove_free_block(block_t **list, block_t *block);

static bool is_small(size_t size);
static bool is_large(size_t size);
static size_t small_idx(size_t size);
static size_t large_idx(size_t size);
static void small_bin_insert(block_t *block, size_t size);
static void large_bin_insert(block_t *block, size_t size);
static void insert_block(block_t *block); // Inserts into a block into some seg list
static void small_bin_remove(block_t *block, size_t size);
static void large_bin_remove(block_t *block, size_t size);
static void remove_block(block_t *block);

static bool get_sixteen(block_t *block);
static bool get_prev_sixteen(block_t *block);
static void write_prev_sixteen(block_t *block, bool prev_sixteen);
static void write_prev_sixteen_of_next_block(block_t *block, bool prev_sixteen);
static block_t *get_sixteen_prev_ptr(block_t *block);
static block_t *get_sixteen_next_ptr(block_t *block);
static block_t *get_next_free_block(block_t *block);
static block_t *get_prev_free_block(block_t *block);

/*
 * Initializes the heap by allocating space for helping data structures and
 * starting space for users.
 */
bool mm_init(void)
{
    // Initialize Static Global Variables.
    MIN_SMALL_BIN_SIZE = min_block_size;
    MAX_SMALL_BIN_SIZE = MIN_SMALL_BIN_SIZE + (NUM_SMALL_BINS - 1) * dsize;
    MIN_LARGE_BIN_SIZE = MAX_SMALL_BIN_SIZE + dsize;

    // Allocate and zero initialize the segregated lists
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

    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1)
    {
        return false;
    }

    start[0] = pack(0, false, false, true, true);  // Prologue footer
    start[1] = pack(0, false, false, false, true); // Epilogue header

    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *)&(start[1]);

    // Extend the empty heap and insert it into the freelist
    block_t *first_ever_block = extend_heap(chunksize);
    if (first_ever_block == NULL)
    {
        return false;
    }

    // Write the metadata
    size_t size = get_size(first_ever_block);
    write_header(first_ever_block, size, false, false, true, false);
    write_header_to_footer(first_ever_block, size);

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
    asize = round_up(size + wsize, dsize);

    // Search the segregated lists for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then place the block
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
 * Given a pointer to a payload created by malloc, free that memory.
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    dbg_printf("Free this block: %p\n", block);

    // Clear the alloc bit of the header. 16-byte blocks lack a footer.
    block->header &= ~alloc_mask;
    if (size != min_block_size)
    {
        write_header_to_footer(block, size);
    }

    block_t *coalesce_ptr = coalesce(block);
    insert_block(coalesce_ptr);
}

/**
 * @brief Changes the size of an already allocated block of memory and
 *          returns a pointer to its new position.
 * 
 * @param ptr Pointer to the already allocated payload created by malloc
 * @param size New size of the allocated block.
 * @return (void*) Pointer to the payload of the resized block
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    dbg_printf("Realloc block:%p, size: %zu\n", block, size);
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

/**
 * @brief Allocates contiguous memory to hold a number of elements.
 * 
 * @param elements The number of elements to allocate for
 * @param size Size of each element in bytes
 * @return (void*) Pointer to the start of the payload
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
 * Extends the heap by size bytes and returns a pointer to the last free block.
 * 
 * Implementation:
 * Always repurposes the dummy epilogue into the header of the last free block
 */
static block_t *extend_heap(size_t size)
{
    dbg_printf("Extend Heap by %zu!", size);
    void *bp;

    // Allocate a free block made of an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }

    // Initialize metadata of the newly created free block
    block_t *block = payload_to_header(bp);
    bool is_size_sixteen = size == min_block_size;

    block->header |= alloc_mask;
    block->header |= (is_size_sixteen << sixteen_bit_offset);
    block->header = (block->header & ~size_mask) | size;

    write_header_to_footer(block, size);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, is_size_sixteen, false, false, true);

    // Coalesce in case the previous block was free
    block_t *coalesce_ptr = coalesce(block);

    // Only remove the block if it's found in the segregated lists
    if (!get_prev_alloc(coalesce_ptr))
    {
        remove_block(coalesce_ptr);
    }
    return coalesce_ptr;
}

/**
 * @brief Merges adjacent free blocks into a single free block and returns
 *          a pointer to the resultant block
 * 
 * @param block 
 * @return block_t* 
 */
static block_t *coalesce(block_t *block)
{
    // 4 Possible Cases
    block_t *next_block = find_next(block);

    // Edge cases? Consider at the ends
    bool prev_is_allocated = get_prev_alloc(block);
    bool next_is_allocated = get_alloc(next_block);

    // Edge cases, attempts to coalesce with the "walls" of a heap should fail.
    if (block == next_block)
    {
        dbg_printf("Coalesce at right edge of heap. %p\n", block);
        next_is_allocated = true;
    }

    if (!prev_is_allocated)
    {
        if (block == find_prev(block))
        {
            dbg_printf("Coalesce at left edge of heap. Block: %p, Prev: %p, Size: %zu\n", block, find_prev(block), get_size(block));
            prev_is_allocated = true;
        }
    }

    if (prev_is_allocated && next_is_allocated)
    {
        // No coalescing required, but add to free_list
        dbg_printf("No Coalesce\n");

        write_prev_alloc_of_next_block(block, false);
        return block;
    }
    else if (prev_is_allocated && !next_is_allocated)
    {
        /* Coalesce with next block */
        dbg_printf("Coalesce with next block\n");

        // Grab metadata
        size_t current_size = get_size(block);
        size_t next_size = get_size(next_block);
        size_t new_size = current_size + next_size;

        // Splice out the next block from free_list
        remove_block(next_block);

        // Create/Update header and footer
        write_coalesce_header(block, new_size);
        write_header_to_footer(block, new_size);
        write_prev_sixteen_of_next_block(block, false);
        return block;
    }
    else if (!prev_is_allocated && next_is_allocated)
    {
        /* Coalesce with the previous block */

        // Grab metadata
        size_t current_size = get_size(block);
        block_t *prev_block = find_prev(block);
        size_t prev_size = get_size(prev_block);
        size_t new_size = current_size + prev_size;

        dbg_printf("Coalesce with previous, block: %p. prev-block: %p\n", block, prev_block);

        // Update free_list
        remove_block(prev_block);

        // Create/Update header and footer
        write_coalesce_header(prev_block, new_size);
        write_header_to_footer(prev_block, new_size);

        // The next block is always allocated. Thus, only update next's header.
        write_prev_alloc_of_next_block(prev_block, false);
        write_prev_sixteen_of_next_block(prev_block, false);

        return prev_block;
    }
    else
    {
        /* Coalesce all 3 blocks */
        dbg_printf("Coalesce 3\n");

        // Grab metadata
        size_t current_size = get_size(block);
        block_t *prev_block = find_prev(block);
        size_t prev_size = get_size(prev_block);
        size_t next_size = get_size(next_block);
        size_t new_size = prev_size + current_size + next_size;

        // List Manipulation
        remove_block(next_block);
        remove_block(prev_block);

        // Update the header and footer of the new merged free block
        write_coalesce_header(prev_block, new_size);
        write_header_to_footer(prev_block, new_size);

        // The next block is always allocated. Thus, only update next's header.
        write_prev_alloc_of_next_block(prev_block, false);
        write_prev_sixteen_of_next_block(prev_block, false);

        return prev_block;
    }
}

/**
 * @brief Efficiently alters the header of a merged block created
 *          in coalesce.
 * 
 * 
 * @param block - the merged block created by coalesce
 * @param new_size - the new size of the merged block
 */
static void write_coalesce_header(block_t *block, size_t new_size)
{
    block->header &= ~alloc_mask;
    block->header &= ~sixteen_mask;
    block->header = (block->header & ~size_mask) | (new_size);
}

/**
 * @brief Allocates a block of asize bytes within a passed free block
 *          that is the same size or larger.
 *          
 * 
 * @param block - The freeblock we will allocate within
 * @param asize - The number of bytes we are going to allocate
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block); // Current Size

    dbg_printf("Place this block: %p, csize: %zu, asize: %zu\n", block, csize, asize);

    if ((csize - asize) >= min_block_size)
    {
        /* Splitting a free block into allocated | split-freeblock */

        block_t *block_next;

        // Allocation, remove the free block
        bool allocated_block_is_sixteen = asize == min_block_size;
        remove_block(block);

        block->header |= alloc_mask;
        block->header |= (allocated_block_is_sixteen << sixteen_bit_offset);
        block->header = (block->header & ~size_mask) | asize;

        // Construct and insert the leftover free block
        block_next = find_next(block);

        bool free_block_is_sixteen = csize - asize == min_block_size;

        write_header(block_next, csize - asize, allocated_block_is_sixteen, free_block_is_sixteen, true, false);
        if (!free_block_is_sixteen)
        {
            write_header_to_footer(block_next, csize - asize);
        }
        else
        {
            // If splitting makes the leftover free block size 16, we must update the block after
            write_prev_sixteen_of_next_block(block_next, true);
        }

        insert_block(block_next);
    }

    else
    {
        /* No splitting required. Therefore remove from free list */
        remove_block(block);

        // Allocation by setting the alloc bit
        block->header |= alloc_mask;

        // The next block is assumed to be allocated
        write_prev_alloc_of_next_block(block, true);
    }
}

/*
 * <what does find_fit do?>
 * Finds a free block that can fit asize.
 * 
 * Currently, First-Fit implementation
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
    else
    {
        size_t idx = large_idx(asize);
        list = &bins->large_bins[idx];
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
            if (block != NULL && (asize <= get_size(block)))
            {
                return block;
            }
        }
        else
        {
            block_t *block = *current_list;
            while (block != NULL)
            {
                if ((asize <= get_size(block)))
                {
                    return block;
                }
                block = get_next_free_block(block);
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
            if (get_next_free_block(current) && current != get_prev_free_block(get_next_free_block(current)))
            {
                print_heap();
                printf("Not Doubly Linked Properly. Neighbors: %p, %p Line: %d\n", current, get_next_free_block(current), line);
                return false;
            }
            current = get_next_free_block(current);
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
            current = get_next_free_block(current);
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
            current = get_next_free_block(current);
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

    // Check if a free block's header == footer. Don't perform if size 16 bit set.
    for (block = heap_start; get_size(block) > 0; block = find_next(block))
    {
        if (!get_alloc(block) && !get_sixteen(block))
        {
            // Only for free blocks
            word_t header = block->header;
            word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
            word_t footer = *footerp;

            if (header != footer)
            {
                printf("Footer and Header of free block don't match. Block: %p\n", block);
                printf("Header: %p; Footer: %p\n", (void *)header, (void *)footer);
                print_heap();
                return false;
            }
        }
    }

    // If a block is size 16, check that its is_sixteen bit is set if allocated.
    // If it's free, impossible to check :(
    for (block = heap_start; get_size(block) > 0; block = find_next(block))
    {
        if (get_alloc(block) && get_sixteen(block))
        {
            if (get_size(block) != min_block_size)
            {
                printf("Sixteen bit is set but different size\n");
                print_heap();
                return false;
            }
        }
    }

    // Check if a block has is_16 set, then the next block has prev_sixteen set
    for (block = heap_start; get_size(find_next(block)) > 0; block = find_next(block))
    {
        if (get_sixteen(block) != get_prev_sixteen(find_next(block)))
        {
            printf("Prev-Sixteen bit mismatch. Block: %p, Next: %p\n", block, find_next(block));
            print_heap();
            return false;
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
static word_t pack(size_t size, bool prev_sixteen, bool sixteen, bool prev_alloc, bool alloc)
{
    return size | prev_sixteen << prev_sixteen_bit_offset | sixteen << sixteen_bit_offset | prev_alloc << prev_alloc_bit_offset | alloc;
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
    if (get_sixteen(block))
    {
        return min_block_size;
    }
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
static void write_header(block_t *block, size_t size, bool prev_sixteen, bool sixteen, bool prev_alloc, bool alloc)
{
    block->header = pack(size, prev_sixteen, sixteen, prev_alloc, alloc);
}

/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool prev_sixteen, bool sixteen, bool prev_alloc, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, prev_sixteen, sixteen, prev_alloc, alloc);
}

/**
 * @brief Copies the header to the footer.
 * 
 * @param block - The block to write the footer on
 * @param size - Size of the passed block
 */
static void write_header_to_footer(block_t *block, size_t size)
{
    word_t *footerp = (word_t *)((block->payload) + size - dsize);
    *footerp = block->header;
}

/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    size_t size = get_size(block);
    block_t *block_next = (block_t *)(((char *)block) + size);
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
    if (get_prev_sixteen(block))
    {
        return (block_t *)((char *)block - min_block_size);
    }
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

/**
 * @brief Prints associated metadata of a block
 * 
 * @param block 
 */
static void print_block(block_t *block)
{
    if (!get_alloc(block))
    {
        if (get_sixteen(block))
        {
            printf("[Addr: %p, Size: %lu, P-Sixt: %u, Sixt: %u, PrevAlloc: %u, Alloc: %u| next: %p, prev: %p]\n",
                   block, get_size(block), get_prev_sixteen(block), get_sixteen(block), get_prev_alloc(block), get_alloc(block), get_sixteen_next_ptr(block), get_sixteen_prev_ptr(block));
        }
        else
        {
            printf("[Addr: %p, Size: %lu, P-Sixt: %u, Sixt: %u, PrevAlloc: %u, Alloc: %u| next: %p, prev: %p]\n",
                   block, get_size(block), get_prev_sixteen(block), get_sixteen(block), get_prev_alloc(block), get_alloc(block), block->next, block->prev);
        }
    }
    else
    {
        printf("[Addr: %p, Size: %lu, P-Sixt: %u, Sixt: %u, PrevAlloc: %u, Alloc: %u]\n",
               block, get_size(block), get_prev_sixteen(block), get_sixteen(block), get_prev_alloc(block), get_alloc(block));
    }
}

/**
 * @brief Prints every block on the heap using implicit traversal.
 * 
 */
static void print_heap()
{
    printf("HEAP DUMP\n");
    block_t *block;
    for (block = heap_start; get_size(block) > 0; block = find_next(block))
    {
        print_block(block);
    }
}

/**
 * @brief Prints every single block held in the segregated lists.
 * 
 */
static void print_free_list()
{
    printf("FREELIST DUMP vvv\n");
    block_t **current_list = bins->small_bins;
    block_t **end = ((bins->small_bins) + NUM_SMALL_BINS + NUM_LARGE_BINS);
    int counter = 0;
    while (current_list != end)
    {
        // Traverse this list
        block_t *current = *current_list;
        while (current != NULL)
        {
            printf("Bin %d: ", counter);
            print_block(current);
            current = get_next_free_block(current);
        }
        counter++;
        current_list++; // Move to the next list
    }
}

/**
 * @brief Inserts a free block into the passed free list.
 *          Helper function, never called directly.
 * 
 * @param list 
 * @param block 
 */
static void insert_free_block(block_t **list, block_t *block)
{
    dbg_printf("Insertion of block: %p\n", block);

    if (*list == NULL)
    {
        if (get_sixteen(block))
        {
            // 16 byte-blocks have a different anatomy than normal blocks.
            // Their next ptr is actually stored in the header position and
            // their prev ptr is store in the next position
            block->header = block->header & (word_t)0xF;
            block->next = NULL;
            *list = block;
        }
        else
        {
            block->next = NULL;
            block->prev = NULL;
            *list = block;
        }
        return;
    }

    if (get_sixteen(block))
    {
        // We have 4 bits of metadata, hence 0xF. B/c 16 byte blocks
        // store their next ptr in the same position as their header,
        // the metadata bits must be spliced on.
        word_t bits = block->header & (word_t)0xF;
        block->header = ((word_t)*list & size_mask) | bits;
        block->next = NULL;

        if (get_sixteen(*list))
        {
            (*list)->next = block;
        }
        else
        {
            (*list)->prev = block;
        }
        *list = block;
    }
    else
    {
        // doubly linked insertion
        block->next = *list;
        block->prev = NULL;
        (*list)->prev = block;

        // The inserted block is now the root
        *list = block;
    }
}

/**
 * @brief Removes a free block from a specified free list.
 * 
 * @param list 
 * @param block 
 */
static void remove_free_block(block_t **list, block_t *block)
{
    dbg_printf("Removal of block: %p\n", block);

    // If a block is size 16, we must act differently
    if (get_sixteen(block))
    {
        // If only a single node, remove it.
        if (*list == block && get_sixteen_prev_ptr(*list) == (*list) && get_sixteen_next_ptr(*list) == *list)
        {
            *list = NULL;
            return;
        }

        // If we are removing the root, change the root.
        if (*list == block)
        {
            *list = get_sixteen_next_ptr(*list); // next ptr is the header
        }

        block_t *splice_block_next = get_sixteen_next_ptr(block);
        block_t *splice_block_prev = get_sixteen_prev_ptr(block);

        if (splice_block_prev != NULL)
        {
            if (get_sixteen(splice_block_prev))
            {
                // Save the first 4 bits
                word_t bits = splice_block_prev->header & (word_t)0xF;
                splice_block_prev->header = ((word_t)splice_block_next & size_mask) | bits;
            }
            else
            {
                splice_block_prev->next = splice_block_next;
            }
        }
        if (splice_block_next != NULL)
        {
            if (get_sixteen(splice_block_next))
            {
                splice_block_next->next = splice_block_prev;
            }
            else
            {
                splice_block_next->prev = splice_block_prev;
            }
        }
    }
    else
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
}

/* vvvvvvvvvvvvvvvvvvvvvvvv Removing Footer Functions vvvvvvvvvvvvvvvvvvvvvvvv */
/**
 * @brief Returns the prev_alloc bit from a block's header.
 * 
 * @param block 
 */
static bool get_prev_alloc(block_t *block)
{
    return (block->header & prev_alloc_mask);
}

/**
 * @brief Overwrites the prev_alloc bit of a block
 * 
 * @param block 
 * @param prev_alloc 
 */
static void write_prev_alloc(block_t *block, bool prev_alloc)
{
    block->header = (block->header & ~prev_alloc_mask) | (prev_alloc << prev_alloc_bit_offset);
}

/**
 * @brief Overwrites the prev_alloc bit of the next adjacent block's header.
 * 
 * @param block 
 * @param prev_alloc Bit value to write
 */
static void write_prev_alloc_of_next_block(block_t *block, bool prev_alloc)
{
    block_t *next_block = find_next(block);
    write_prev_alloc(next_block, prev_alloc);
}

/* vvvvvvvvvvvvvvvvvv Segregated List Helper Functions vvvvvvvvvvvvvvvvvv */
/**
 * @brief Determines if a passed size would go into a small bin.
 * 
 * @param size 
 */
static bool is_small(size_t size)
{
    return size <= MAX_SMALL_BIN_SIZE;
}

/**
 * @brief 
 * 
 * @param size 
 * @return true 
 * @return false 
 */
static bool is_large(size_t size)
{
    return !is_small(size);
}

/**
 * @brief Calculates the index of the small bin a block would be placed in.
 * 
 * @param size 
 * @return size_t 
 */
static size_t small_idx(size_t size)
{
    return (size - MIN_SMALL_BIN_SIZE) / dsize;
}

/**
 * @brief Calculates the index of the large bin a block would be placed in.
 * 
 * @param size 
 * @return size_t 
 */
static size_t large_idx(size_t size)
{
    size_t idx = log2l(size - MAX_SMALL_BIN_SIZE - dsize) - 4;
    if (idx >= NUM_LARGE_BINS)
    {
        return NUM_LARGE_BINS - 1;
    }
    return idx;
}

/**
 * @brief Inserts a block into a small bin. Helper function to insert_block
 * 
 * @param block
 * @param size 
 */
static void small_bin_insert(block_t *block, size_t size)
{
    size_t small_list_idx = small_idx(size);
    block_t **list_head = &bins->small_bins[small_list_idx];
    insert_free_block(list_head, block);
}

/**
 * @brief Inserts a block into a large bin. Helper function to insert_block
 * 
 * @param block 
 * @param size
 */
static void large_bin_insert(block_t *block, size_t size)
{
    size_t large_list_idx = large_idx(size);
    block_t **list_head = &bins->large_bins[large_list_idx];
    insert_free_block(list_head, block);
}

/**
 * @brief Inserts a block into the correct bin
 * 
 * @param block 
 */
static void insert_block(block_t *block)
{
    size_t size = get_size(block);
    if (is_small(size))
    {
        small_bin_insert(block, size);
    }
    else
    {
        large_bin_insert(block, size);
    }
}

/**
 * @brief Removes a block from a small bin. Helper function to remove_block().
 * 
 * @param block 
 * @param size
 */
static void small_bin_remove(block_t *block, size_t size)
{
    int small_list_idx = small_idx(size);
    block_t **list_head = &bins->small_bins[small_list_idx];
    remove_free_block(list_head, block);
}

/**
 * @brief Removes a block from a large bin. Helper function to remove_block().
 * 
 * @param block 
 * @param size
 */
static void large_bin_remove(block_t *block, size_t size)
{
    size_t large_list_idx = large_idx(size);
    block_t **list_head = &bins->large_bins[large_list_idx];
    remove_free_block(list_head, block);
}

/**
 * @brief Removes a block from the correct bin.
 * 
 * @param block 
 */
static void remove_block(block_t *block)
{
    size_t size = get_size(block);
    if (is_small(size))
    {
        small_bin_remove(block, size);
    }
    else
    {
        large_bin_remove(block, size);
    }
}

/* vvvvvvvvvvvvvvvvvvvvv 16 Byte Min-Block Size Functions vvvvvvvvvvvvvvvvvvvvvvv*/
/**
 * @brief Returns the value of the "has size 16" bit from a block's header
 * 
 * @param block 
 */
static bool get_sixteen(block_t *block)
{
    return (block->header & sixteen_mask);
}

/**
 * @brief Get the value of the "previous block has size 16" from a block's
 *          header
 * 
 * @param block 
 */
static bool get_prev_sixteen(block_t *block)
{
    return (block->header & prev_sixteen_mask);
}

/**
 * @brief Overwrites the prev_sixteen bit of a block.
 * 
 * @param block 
 * @param prev_sixteen 
 */
static void write_prev_sixteen(block_t *block, bool prev_sixteen)
{
    block->header = (block->header & ~prev_sixteen_mask) | (prev_sixteen << prev_sixteen_bit_offset);
}

/**
 * @brief Overwrites the prev_sixteen bit of a block's next neightboring block.
 * 
 * @param block 
 * @param prev_sixteen 
 */
static void write_prev_sixteen_of_next_block(block_t *block, bool prev_sixteen)
{
    block_t *next_block = find_next(block);
    write_prev_sixteen(next_block, prev_sixteen);
}

/**
 * @brief Returns the next pointer of a size 16 block.
 *          
 *          This is necessary b/c size 16 blocks mutate
            the 4th bit for metadata and are structured
            differently than normal blocks.
 * 
 * @param block 
 * @return block_t* 
 */
static block_t *get_sixteen_next_ptr(block_t *block)
{
    if ((block->header & size_mask) == 0)
    {
        return NULL;
    }
    return (block_t *)((block->header & size_mask) | prev_sixteen_mask);
}

/**
 * @brief Returns the prev pointer of a size 16 block.
 * 
 *          This is necessary b/c size 16 are structured
            differently than normal blocks.
 * 
 * @param block 
 * @return block_t* 
 */
static block_t *get_sixteen_prev_ptr(block_t *block)
{
    return block->next;
}

/**
 * @brief Returns a block's next ptr.
 *          
 *          This is necessary b/c we have two different
 *          types of blocks that access their next pointer
 *          differently.
 * 
 * @param block 
 * @return block_t* 
 */
static block_t *get_next_free_block(block_t *block)
{
    if (get_sixteen(block))
    {
        return get_sixteen_next_ptr(block);
    }
    return block->next;
}

/**
 * @brief Returns a block's prev ptr.
 *          
 *          This is necessary b/c we have two different
 *          types of blocks that access their prev pointer
 *          differently.
 * 
 * @param block 
 * @return block_t* 
 */
static block_t *get_prev_free_block(block_t *block)
{
    if (get_sixteen(block))
    {
        return get_sixteen_prev_ptr(block);
    }
    return block->prev;
}
