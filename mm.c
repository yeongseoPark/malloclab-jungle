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
 * 
 * 일단 implicit 방법으로 구현
 * - 
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
/* 
    - size 2 , ALIGNMENT 8 가정
        - ~0x7
            : 11111111 11111111 11111111 11111000 -> -8
        - (2 + (8-1)) & 11111111 11111111 11111111 11111000
            : 00000000 00000000 00000000 00001000 -> 8

    - size 10, ALIGNMENT 8 가정
        - (10 + (8-1)) & 1111111 11111111 11111111 11111000
        : 00000000000000000000000000010000 -> 16
 */

/* ALIGN(4)와 같다. (4 + 7) & ~0x7 = 8 
    헤더와 푸터를 위해 필요한 DWORD크기 메모리
*/
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


/* 가용 리스트 조작을 위한 기본 상수 및 매크로 정의 */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)  // 4096 - heap을 해당 크기(바이트)만큼 연장함

#define MAX(x,y) ((x) > (y) ? (x) : (y))

/* 크기와 할당비트 통합하여 헤더와 푸터에 저장할 값 리턴 */
#define PACK(size, alloc) ((size) | (alloc)) 
/* 
    size 7, 할당비트 8 이면 
    7 : 0000 0111
    8 : 0000 1000 
    7 | 8 = 0000 1111
    : 15

    size 3, 할당비트 2 이면 
    3 : 0000 0011
    2 : 0000 0010 
    3 | 2 = 0000 0011
    : 3

    size 3, 할당비트 4이면
    3 : 0000 0011
    4 : 0000 0010
    3 | 4  = 0000 0111
    : 7
*/

/* 인자 p가 참조하는 워드를 읽어서 리턴 
    - p가 대개 void포인터이기 때문에 이를 직접적으로 역참조할 수 없어서 type casting
*/
#define GET(p)       (*(unsigned int *)(p))
/* 인자 p가 가리키는 워드에 val을 저장 */
#define PUT(p, val)  (*(unsigned int *)(p)) = (val)

/* 주소 p에 있는 헤더 또는 푸터의 바이트 size를 리턴
    : p에 0x19(10진수로 25)가 저장돼있다 치자,
    해당 연산은 & ~0x7을 통해 하위 3비트를 지워준다.
    그래서 25에 대해 GET_SIZE(25)를 하면, 결과로 0x18(10진수로 24)가 나오는데
    이는 할당연산자 1을 제외한 결과와 같기때문에, 해당 헤더에 들어있는 사이즈가 맞다

    => & ~0x7로 마지막3비트를 제거해서 8의 배수로 정렬된 값으로 계산하는 것!
 */
#define GET_SIZE(p) (GET(p) & ~0x7)

/* 주소 p에 있는 헤더 또는 푸터의 할당비트를 리턴
    : & 0x1 로 마지막 비트를 "추출"하는거네!
 */
#define GET_ALLOC(p) (GET(p) & 0x1)  

/* block포인터 bp를 가지고, 블록헤더를 가리키는 포인터 리턴 
    - 블록포인터는 payload를 가리키기 때문에, 한 word만큼 포인터연산을 해준다(char포인터니까 4비트만큼 빼준것)
*/
#define HDRP(bp) ((char *)(bp) - WSIZE)
/* block포인터 bp를 가지고, 블록풋터를 가리키는 포인터를 리턴 
    - 일단 GET_SIZE(HDRP(bp))로 헤더에 있는 사이즈(헤더+페이로드+푸터+패딩)를 얻어온다,
    - 그리고 이를 payload의 시작점에 더해줌
    - 여기서 더블워드만큼 빼주면 푸터가 나옴
    ex) bp가 1이고 사이즈가 24, 둘이 더해주면 25인데, 블록은 0(헤더) ~ 23까지 존재하기 때문에
    더블워드만큼 빼주면 푸터값에 대한 포인터가 맞다
*/
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 다음 블록의 블록포인터를 리턴 
    ex) 
    0 : 헤더의 위치 - 24바이트 기록
    1 : bp의 위치(payload의 시작)
    24 : 다음 블록의 헤더위치
    25 : 다음 블록의 페이로드 시작점
    1 + 24(헤더에서 가져온 사이즈) = 다음 블록의 페이로드 시작점
*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
/* 이전 블록의 블록포인터를 리턴
    ex)
    bp의 위치 25
    이전 블록의 푸터로 가서 ((char *)(bp) - DSIZE) : 23
    거기서 얻어낸 사이즈만큼 빼줌
    사이즈가 5라고 가정하면
    23 - 5 = 18가 이전 블록 페이로드의 시작점 
 */
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Free list에서의 이전 , 이후의 "포인터"를 리턴  */
/* 1.  bp 포인터(=PRED 포인터)를 void 포인터를 가리키는 포인터로 형변환 
    PREC 자체가 이전을 가리키는 void 포인터, 이를 가리키는 이중 포인터를 만든 후
    해당 포인터에 대해 indirection을 해주면 직전 포인터로 넘어갈 수 있다
*/
#define PREC_FREEP(bp) (*(void**)(bp)) 
/* 2. 위의 메커니즘과 마찬가지이나, 한칸 앞으로 가서 SUCC 포인터에 대해 연산해주면 됨 */
#define SUCC_FREEP(bp) (*(void**)(bp + WSIZE))


static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void removeBlock(void *bp);
static void putFreeBlock(void *bp); 

static char* heap_listp; // 포인터 연산시 1바이트씩 이동시키기 위해 static char 사용
static char* free_listp; /* 가용 연결 리스트 */

/* 
 * mm_init - initialize the malloc package.
 : 필요한 초기화 수행
    - 초기의 힙 영역 할당 등
    - 초기화에 문제가 있다면 -1 리턴
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1) // 시스템에서 4워드를 가져옴, 문제생기면 -1리턴
        return -1;

    PUT(heap_listp, 0);  // 패딩
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE * 2, 1)); /* 프롤로그 헤더 - 프롤로그 블록 사이즈 = 푸터 + 헤더 + prev + next = 16 */ 
    PUT(heap_listp + (2*WSIZE), NULL);                /* PREC */
    PUT(heap_listp + (3*WSIZE), NULL);                /* SUCC */
    PUT(heap_listp + (4*WSIZE), PACK(DSIZE * 2, 1));  /* 프롤로그 푸터 */
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));          /* 에필로그 헤더 */
    free_listp  = heap_listp + 2 * WSIZE;            // 가용 연결리스트의 시작점 = 맨처음 PREC
    // heap_listp += (2*WSIZE);                         // 프롤로그 푸터위치로 이동 

    /* 힙을 CHUNKSIZE만큼 확장 */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) // CHUNKSIZE(바이트)에 WSIZE로 나눠주어서 워드로 변환
        return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * : 최소 size 바이트의 할당된 블록에 대한 포인터를 리턴
 *  - 전체 할당된 블록은 힙 영역에 있어야 하고, 다른 할당된 chunk와 겹치면 안됨
 *  - 8 바이트의 aligned된 포인터 리턴?
 */
void *mm_malloc(size_t size)
{
    size_t asize; // adjusted size
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    /* 정렬 요건과 오버헤드를 포함할 수 있도록 블록 사이즈를 조정
       ALIGN(요청 사이즈 + 헤더와 푸터를 위한 DWORD) 
     */
    asize = ALIGN(size + SIZE_T_SIZE);
    
    /* First-Fit 가용 공간 추적 후 공간 할당 */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    } 

    /* 적절한 fit을 찾지 못했음 - 메모리 요청 더하고 블록 위치시킴 */
    extendsize = MAX(asize, CHUNKSIZE); 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) 
        return NULL;
    place(bp, asize); 
    return bp;
}

/* 
    1. 힙이 초기화될 때
    2. mm_malloc이 적당한 맞춤 fit을 찾지 못했을때
    -> 두가지 경우에서 호출됨

    - 요청받는 words는 "워드"
    - 이 "워드"는 무조건 8의 배수로 값이 들어옴
*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 요청한 크기를 정렬을 유지하기 위해 인접 2워드의 배수(8바이트)로 올림 (워드단위로 인자가 들어옴)
     */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) // 메모리 시스템에게 추가적인 힙 공간 요청 -> bp는 새로이 할당받은 공간의 시작주소 가리킴
        return NULL; // 예외처리
    
    /* free block의 헤더/푸터 초기화 , 에필로그 헤더 옮김 */
    PUT(HDRP(bp), PACK(size, 0)); // 새 가용 블록의 헤더 - 기존 에필로그 헤더를 새로이 할당받은 블록의 헤더로 바꿈
    PUT(FTRP(bp), PACK(size, 0)); // 새 가용 블록의 푸터 
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 에필로그 블록 헤더 - 새로운 program_break 

    /* 이전 블록이 free라면 두개의 가용 블록을 통합후 통합된 블록의 블록 포인터 리턴  */
    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* 이전과 다음 블록 모두 할당된 경우 */
    if (prev_alloc && next_alloc) {
        // 해당 블록만 free list에 삽입하면 됨
    }

    /* 이전 블록 할당, 다음 블록은 free 
        : free 상태였던 직후 블록을 free list에서 삭제, 새로운 가용 블록을 free list에 삽입
    */
    else if (prev_alloc && !next_alloc) {
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    /* 이전 블록은 free, 다음 블록은 할당됨 
        : free 상태였던 직전 블록을 free list에서 삭제, 새로운 가용 블록을 free list에 삽입
    */
    else if (!prev_alloc && next_alloc) {
        removeBlock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp); 
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    
    /* 이전과 다음 블록 모두 free
        : 직전, 직후 블록 모두 free list에서 삭제, 새로운 가용 블록을 free list에 삽입 
     */
    else {
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(FTRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    /* 새 가용 블록을 free list에 추가 */
    putFreeBlock(bp);

    return bp;
}



/* First - Fit */
static void *find_fit(size_t asize) 
{
    void *bp;

    /* free list의 맨 뒤는 프롤로그 블록, 이는 free list에서 유일하게 "할당된"(비트가 1인)블록이므로, 얘를 만나면 탐색 종료
        -> free list의 맨 뒤에 어떻게 프롤로그 블록이 들어가는지 이해 안됨. init에서 heap_listp와 free_listp 위치가 이해 안되는 것과 연결된문제인듯
     */
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)) { 
        if (asize <= GET_SIZE(HDRP(bp))) 
            return bp;
    }

    return NULL; // NO fit
}

/* 
    요구 메모리를 할당할 수 있는 가용블록을 할당.
    가용 블록의 분할 방식 중 - "분할" 방식 선택(가용 블록을 두 부분으로 나눔) */
static void place(void *bp, size_t asize)
{
    /* 현재 가용블록의 크기 */
    size_t csize = GET_SIZE(HDRP(bp));
    
    /* 할당될 블록이므로 free list에서 없애준다 */
    removeBlock(bp);

    /* 최소 가용 블록의 크기는 16바이트(헤더+푸터+succ+prec) - 분할 가능한 경우 */
    if ((csize - asize) >= (2*DSIZE)) { // 현재 블록사이즈 - 할당받을 사이즈가 16이상이면, 해당 블록을 나눌 수 있음
        PUT(HDRP(bp), PACK(asize , 1)); // 첫번째 블록에 asize만큼의 공간 할당
        PUT(FTRP(bp), PACK(asize , 1));
        bp = NEXT_BLKP(bp); // 두번째 블록에는 나머지 공간(이거는 가용한 공간)
        PUT(HDRP(bp), PACK(csize - asize , 0));
        PUT(FTRP(bp), PACK(csize - asize , 0));

        /* free list첫번째에 분할된 가용 블럭 넣는다 */
        putFreeBlock(bp);
    }
    /* 분할 불가능한 경우 */
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* extend나 분할을 통해서 새로 생성된 가용 블럭을 free list의 처음에 넣는다(Insertion method중 LIFO 방식) */
static void putFreeBlock(void *bp)
{
    SUCC_FREEP(bp) = free_listp; // 새 블럭의 이후 블럭을 가용 연결 리스트의 시작점으로 
    PREC_FREEP(bp) = NULL;       // 새 블럭의 이전 블럭을 NULL로
    PREC_FREEP(free_listp) = bp; // 가용 연결리스트의 시작점의 이전 블럭을 새로 생성된 가용 블럭으로
    free_listp = bp;             // 가용 연결리스트의 시작점 자체를 bp로
}

/* (연결면서 가용블록의 bp가 아니게 된) OR (새로이 할당된) 블록을 free list에서 없앤다 */
static void removeBlock(void *bp) 
{
    /* free list의 첫번째 블록을 없앨 때 */
    if (bp == free_listp) {
        PREC_FREEP(SUCC_FREEP(bp)) = NULL; // 다음 블록의 이전을 NULL로 처리 
        free_listp = SUCC_FREEP(bp);       // 가용 블록 연결리스트의 시작점을 없애는 블록의 다음 블록으로 설정
    }
    /* free list 안의 블록을 없앨 때 */
    else {
        PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp); // 현재의 이후 블록의 이전 블럭을 없애는 블럭의 이전 블럭으로
        SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp); // 현재의 이전 블록의 이후 블록을 없애는 블럭의 이후 블럭으로 
    }
}


/*
 * mm_free - Freeing a block does nothing.
 : ptr이 가리키고 있는 블럭을 free, 아무것도 반환하지 않음
    - mm_malloc이나 mm_realloc호출을 통해 받았고, 아직 free 되지 않은 포인터가 넘겨졌을때만 작동
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 - 최소 size 바이트의 할당된 영역에 대한 포인터를 반환
    - ptr이 NULL이면 mm_malloc(size)와 같다
    - size가 zero라면 mm_free(ptr)과 같다
    - ptr이 NULL이 아니라면, 이는 mm_malloc이나 mm_realloc을 통해 리턴받은 것이어야만 한다.
    - mm_realloc은 ptr이 가리키고 있는 메모리 블록을 size byte로 바꾸고, 새로운 블록의 주소를 반환
        - 이때 새로운 블록의 주소는 "구현방식" 과 "기존 블록의 internal fragmentation"에 따라 이전 블록의 주소와 같거나, 다를 수 있다 
        - 새로운 블록의 내용은 이전 ptr블록의 내용과 같다.
        - 만약 구 블록이 8바이트고, 새로운 블록이 12바이트라면, 새 블록의 첫 8바이트는 구 블록의 첫 8바이트와 같고,
        - 나머지 4바이트는 uninitialized된 상태이다.
        - 마찬가지로, 구 블록이 8바이트이고, 새 블록이 4바이트라면
        - 새 블록의 내용은 구 블록의 첫 4 바이트와 같다.
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newPtr;
    size_t copySize;

    newPtr = mm_malloc(size);
    if (newPtr == NULL)
        return NULL;

    copySize = GET_SIZE(HDRP(oldptr));

    if (size < copySize) {
        copySize = size;
    }

    memcpy(newPtr, oldptr, copySize);
    mm_free(oldptr);
    return newPtr;

    // size_t asize;
    // if (size <= DSIZE)
    //     asize = 2 * DSIZE; 
    // else 
    //     asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // // 새로이 할당받을 사이즈가 이전 사이즈보다 작으면
    // if (asize <= old_size) 
    // {
    //     // 기존 사이즈를 줄여주면 됨
    //     place(ptr, asize);
    //     return ptr;
    // } 
    // // 새로이 할당받을 사이즈가 이전 사이즈보다 크면
    // else 
    // {
    //     new_ptr = mm_malloc(asize); // 새로 malloc으로 공간할당받고,
    //     memcpy(new_ptr, ptr, old_size); // 해당 공간을 가리키는 포인터에 기존 값 복사
    //     mm_free(ptr); // 기존 포인터 해제
    //     return new_ptr;
    // }
}














