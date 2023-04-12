/*
 * mm.c - malloc using segregated list
 * KAIST
 * Tony Kim
 * 
 * In this approach, 
 * Every block has a header and a footer 
 * in which header contains reallocation information, size, and allocation info
 * and footer contains size and allocation info.
 * Free list are tagged to the segregated list.
 * Therefore all free block contains pointer to the predecessor and successor.
 * The segregated list headers are organized by 2^k size.
 * 
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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


// My additional Macros
#define WSIZE     4          // word and header/footer size (bytes)
#define DSIZE     8          // double word size (bytes)
#define INITCHUNKSIZE (1<<6)
#define CHUNKSIZE (1<<12)//+(1<<7) 

#define LISTLIMIT     20      
#define REALLOC_BUFFER  (1<<7)    

#define MAX(x, y) ((x) > (y) ? (x) : (y)) 
#define MIN(x, y) ((x) < (y) ? (x) : (y)) 

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word at address p 
#define GET(p)            (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// Store predecessor or successor pointer for free blocks 
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

// Read the size and allocation bit from address p 
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1) // A태그 확인
#define GET_TAG(p)   (GET(p) & 0x2) // RA태그 확인

// Address of block's header and footer 
#define HDRP(ptr) ((char *)(ptr) - WSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

// Address of (physically) next and previous blocks 
#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))
#define PREV_BLKP(ptr) ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))

// Address of free block's predecessor and successor entries 
#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)

// Address of free block's predecessor and successor on the segregated list 
#define PRED(ptr) (*(char **)(ptr))
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))


// End of my additional macros


// Global var
void *segregated_free_lists[LISTLIMIT]; 


// Functions
static void *extend_heap(size_t size);
static void *coalesce(void *ptr);
static void *place(void *ptr, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);

//static void checkheap(int verbose);


///////////////////////////////// Block information /////////////////////////////////////////////////////////
/*
 
A   : Allocated? (1: true, 0:false)
RA  : Reallocation tag (1: true, 0:false)
 
 < Allocated Block >
 
 
             31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |  | A|
    bp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                                                                                               |
            |                                                                                               |
            .                              Payload and padding                                              .
            .                                                                                               .
            .                                                                                               .
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 
 
 < Free block >
 
             31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |RA| A|
    bp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                        pointer to its predecessor in Segregated list                          |
bp+WSIZE--> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                        pointer to its successor in Segregated list                            |
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            .                                                                                               .
            .                                                                                               .
            .                                                                                               .
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 
 
*/
///////////////////////////////// End of Block information /////////////////////////////////////////////////////////

//////////////////////////////////////// Helper functions //////////////////////////////////////////////////////////
static void *extend_heap(size_t size)
{
    void *ptr;                   
    size_t asize;                // Adjusted size 
    
    asize = ALIGN(size);
    
    if ((ptr = mem_sbrk(asize)) == (void *)-1)
        return NULL;
    
    // Set headers and footer 
    PUT(HDRP(ptr), PACK(asize, 0));  
    PUT(FTRP(ptr), PACK(asize, 0));   
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); 
    insert_node(ptr, asize);

    return coalesce(ptr);
}

static void insert_node(void *ptr, size_t size) {
    int list = 0;
    void *search_ptr = ptr;
    void *insert_ptr = NULL;
    
    // Select segregated list 
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++; 
    }
    
    // Keep size ascending order and search
    search_ptr = segregated_free_lists[list];
    /* 가용 리스트는 오름차순 정렬, 역으로 탐색하다 자기 자리가 나오면 탐색 멈춤 */
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = PRED(search_ptr);
    }
    
    // Set predecessor and successor 
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else {
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr;
        }
    } else { // search_ptr이 NULL
        if (insert_ptr != NULL) { 
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else { // insert_ptr도 NULL이어서 아예 
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr;
        }
    }
    
    return;
}


static void delete_node(void *ptr) {
    int list = 0; // segregated_free_list에서의 인덱스 역할

    size_t size = GET_SIZE(HDRP(ptr)); // 삭제하려는 노드의 사이즈
    // Select segregated list 
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1; 
        list++;
    }
    
    if (PRED(ptr) != NULL) {
        if (SUCC(ptr) != NULL) {
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr)); 
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr)); // PREV -> SUCC
        } else {
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
            segregated_free_lists[list] = PRED(ptr); // PREV(크기 클래스의 시작점) -> NULL
        }
    } else {
        if (SUCC(ptr) != NULL) {
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL); // NULL -> PREV
        } else {
            segregated_free_lists[list] = NULL; // 이 크기 클래스에 하나밖에 없었으므로, 그냥 지워줌 
        }
    }
    
    return;
}


static void *coalesce(void *ptr)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    if (prev_alloc && next_alloc) {                         // Case 1 : 둘다 할당돼있어서 합침x
        return ptr;
    }
    else if (prev_alloc && !next_alloc) {                   // Case 2 : 다음 노드는 free, ptr유지한채 사이즈만 늘려주고 헤더 푸터 표시 
        delete_node(ptr);   
        delete_node(NEXT_BLKP(ptr)); // 현재 노드와 다음 노드 가용 연결리스트에서 삭제
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {                 // Case 3 : 이전 노드가 free, ptr을 이전 노드의 bp로 이동, 사이즈에 맞게 헤더와 푸터 표시 
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr)); // 현재 노드와 이전 노드 가용 연결리스트에서 삭제
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    } else {                                                // Case 4 : 앞, 뒤 노드가 다 free, ptr을 이전 노드의 bp로 이동, 사이즈에 맞게 헤더와 푸터 표시
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        delete_node(NEXT_BLKP(ptr)); // 이전, 현재 , 다음 노드 모두 가용 연결리스트에서 삭제
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr))); // 이전, 다음 노드의 사이즈 모두 더해줌
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    
    insert_node(ptr, size); // 가용 연결블럭의 bp인 ptr을 segregated_free_list에 더해줌
    
    return ptr;
}

static void *place(void *ptr, size_t asize)
{
    size_t ptr_size = GET_SIZE(HDRP(ptr));
    size_t remainder = ptr_size - asize;
    
    delete_node(ptr); // segregated_free_list에서 적절한 연결리스트를 찾아서, ptr을 제거해줌
    
    if (remainder <= DSIZE * 2) { // 분할할 수 없음 
        // Do not split block 
        PUT(HDRP(ptr), PACK(ptr_size, 1)); 
        PUT(FTRP(ptr), PACK(ptr_size, 1)); 
    }
    
    /* 큰 블록에 대해서는 뒤쪽 블럭할당 */
    else { 
        // Split block
        PUT(HDRP(ptr), PACK(remainder, 0)); 
        PUT(FTRP(ptr), PACK(remainder, 0));

        PUT(HDRP(NEXT_BLKP(ptr)), PACK(asize, 1));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(asize, 1));
        insert_node(ptr, remainder); // 분할한 가용 블럭 segregate_free_list 어딘가에 넣음
        return NEXT_BLKP(ptr); // 할당 블럭에 대한 포인터 리턴
    }

    return ptr;
}
//////////////////////////////////////// End of Helper functions ////////////////////////////////////////

/*
 * mm_init - initialize the malloc package.
 * Before calling mm_malloc, mm_realloc, or mm_free, 
 * the application program calls mm_init to perform any necessary initializations,
 * such as allocating the initial heap area.
 *
 * Return value : -1 if there was a problem, 0 otherwise.
 */
int mm_init(void)
{
    int list;         
    char *heap_start; // Pointer to beginning of heap
    
    // Initialize segregated free lists
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }
    
    // Allocate memory for the initial empty heap 
    if ((long)(heap_start = mem_sbrk(4 * WSIZE)) == -1)
        return -1;
    
    PUT(heap_start, 0);                            /* Alignment padding */
    PUT(heap_start + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_start + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_start + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;
    
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 *
 * Role : 
 * 1. The mm_malloc routine returns a pointer to an allocated block payload.
 * 2. The entire allocated block should lie within the heap region.
 * 3. The entire allocated block should overlap with any other chunk.
 * 
 * Return value : Always return the payload pointers that are alligned to 8 bytes.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *ptr = NULL;  /* Pointer */
    
    // Ignore size 0 cases
    if (size == 0)
        return NULL;
    
    // Align block size
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = ALIGN(size+DSIZE);
    }
    
    int list = 0; 
    size_t searchsize = asize;

    // Search for free block in segregated list
    while (list < LISTLIMIT) {
        /* segregated_list에서 asize를 포함할 수 있는 크기 클래스에 도달했다면 */
        if ((list == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != NULL))) {
            ptr = segregated_free_lists[list];
            // 연결 리스트를 뒤로 탐색하면서 ... 근데 사실 제일 큰 공간이 연결리스트의 맨 뒤에 있기때문에, 
            // 연결리스트의 맨 뒤(제일 큰 공간)에 할당해주는 느낌이네
            // 스택같이 제일 뒤(제일 큰) 공간이 LIFO형식으로 할당됨
            // 만약 해당 연결리스트의 맨 뒤 공간이 asize보다 작다면, 무조건 연결리스트 맨 끝까지 가게 되고,
            // 다음 크기 클래스로 넘어가게 됨
            while ((ptr != NULL) && ((asize > GET_SIZE(HDRP(ptr)))))
            {   
                ptr = PRED(ptr);
            }
            if (ptr != NULL) // 해당 연결리스트에서 적절한 공간 찾은 경우(연결리스트 맨 뒤가 충분히 큰 경우)
                break;
        }
        
        searchsize >>= 1;
        list++;
    }
    
    // if free block is not found, extend the heap
    if (ptr == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);
        
        if ((ptr = extend_heap(extendsize)) == NULL)
            return NULL;
    }
    
    // Place and divide block
    ptr = place(ptr, asize);
    
    
    // Return pointer to newly allocated block 
    return ptr;
}

/*
 * mm_free - Freeing a block does nothing.
 *
 * Role : The mm_free routine frees the block pointed to by ptr
 *
 * Return value : returns nothing
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
 
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    
    insert_node(ptr, size); // seg_list 어딘가 적절한 곳에 삽입
    coalesce(ptr);
    
    return;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free

 */
void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr = ptr;    /* Pointer to be returned */
    size_t new_size = size; /* Size of new block */
    int remainder;          /* Adequacy of block sizes */
    int extendsize;         /* Size of heap extension */
    
    // Ignore size 0 cases
    if (size == 0)
        return NULL;
    
    // Align block size
    if (new_size <= DSIZE) {
        new_size = 2 * DSIZE;
    } else {
        new_size = ALIGN(size+DSIZE);
    }
    
    /* Check if next block is a free block or the epilogue block */
    if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) { // 현재 ptr 다음 블록이 free이거나 에필로그 블록 
        /* 1. 다음 블록을 사용하는 경우 */
        /* remainder: 현재 블록에 가용한 다음 블럭의 크기를 더한것에서, 새로 할당할 사이즈를 뺀 것 */
        remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size; 
        if (remainder < 0) { // ,...?
            extendsize = MAX(-remainder, CHUNKSIZE); // remainder의 역수와 CHUNKSIZE중 더 큰것 만큼 
            if (extend_heap(extendsize) == NULL)     // 힙을 연장해줌
                return NULL;
            remainder += extendsize;                // 연장한만큼 remainder에 더해준다
        }
        
        delete_node(NEXT_BLKP(ptr));
        
        /* 경우에 따른 블럭의 크기 */
        // if ptr+next 크기 >= new_size:
            // ptr + next 블럭 사이즈만큼 사이즈 잡아줌 
        //  if -remainder > CHUNK && ptr+next 크기 < new_size 크기:
            // ptr + next - new + (-ptr - next + new) + new_size = new_size 만큼 사이즈 잡아줌 
        // elif -remainder < CHUNK && ptr+next 크기 < new_size 크기:
            // ptr + next - new_size + CHUNK + new_size = ptr + next + CHUNKSIZE 만큼 사이즈 잡아줌 
        PUT(HDRP(ptr), PACK(new_size + remainder, 1)); 
        PUT(FTRP(ptr), PACK(new_size + remainder, 1)); 
    } else { // 다음 블록이 할당블록
        /* 2. 다음 블록을 사용하지 않는 경우 */
        new_ptr = mm_malloc(new_size - DSIZE); // 헤더,푸터만큼의 사이즈 빼고 새로 할당해줌
        memcpy(new_ptr, ptr, new_size);
        mm_free(ptr);
    }
    
    // Return the reallocated block 
    return new_ptr;
}
