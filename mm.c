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

/* rounds up to the nearest multiple of ALIGNMENT 

*/
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

/* 특정 자료형의 사이즈에 가장 가까운(올림 한) multiple of ALIGNMENT 값 */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


/* 가용 리스트 조작을 위한 기본 상수 및 매크로 정의 */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)  // 4096 - heap을 해당 크기(바이트)만큼 연장함

#define MAX(x,y) ((x) > (y) ? (x) : (y))

/* 크기와 할당비트 통합하여 헤더와 푸터에 저장할 수 있는 값 리턴 */
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
#define PUT(p, val)  (*(unsigned int *)(p)) = (val)
/* 인자 p가 가리키는 워드에 val을 저장 */

/* 주소 p에 있는 헤더 또는 푸터의 size를 리턴?
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


/* 
 * mm_init - initialize the malloc package.
 : 필요한 초기화 수행
    - 초기의 힙 영역 할당 등
    - 초기화에 문제가 있다면 -1 리턴
 */
int mm_init(void)
{
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * : 최소 size 바이트의 할당된 블록에 대한 포인터를 리턴
 *  - 전체 할당된 블록은 힙 영역에 있어야 하고, 다른 할당된 chunk와 겹치면 안됨
 *  - 8 바이트의 aligned된 포인터 리턴?
 * 
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 : ptr이 가리키고 있는 블럭을 free, 아무것도 반환하지 않음
    - mm_malloc이나 mm_realloc호출을 통해 받았고, 아직 free 되지 않은 포인터가 넘겨졌을때만 작동
 */
void mm_free(void *ptr)
{
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
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














