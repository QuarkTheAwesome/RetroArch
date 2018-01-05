/****************************************************************************
 * Copyright (C) 2015 Dimok
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 ****************************************************************************/
#include <malloc.h>
#include <string.h>
#include <stdbool.h>
#include <stdio.h>
#include "memory.h"
#include <wiiu/mem.h>
#include <wiiu/os.h>
#include "wiiu_dbg.h"

/* Leak detection! Woo! */
typedef struct _lsan_allocation {
   bool allocated;
   void* addr;
   size_t size;
   void* owner;
} lsan_allocation;
#define LSAN_ALLOCS_SZ 0x10000
static lsan_allocation lsan_allocs[LSAN_ALLOCS_SZ];
void net_print(const char *str);

static MEMExpandedHeap* mem1_heap;
static MEMExpandedHeap* bucket_heap;
static MEMExpandedHeap* asan_heap;
static void* asan_heap_mem;
static unsigned int asan_sz;

static void* asan_shadow;
static unsigned int asan_shadow_off;
static bool asan_ready = false;

#define MEM_TO_SHADOW(ptr) (unsigned char*)((((void*)ptr - asan_heap_mem) >> 3) + asan_shadow)
#define SET_SHADOW(shadow, ptr) (*shadow) |= 1 << ((unsigned int)ptr & 0x7)
#define CLR_SHADOW(shadow, ptr) (*shadow) &= ~(1 << ((unsigned int)ptr & 0x7))
#define GET_SHADOW(shadow, ptr) (*shadow >> ((unsigned int)ptr & 0x7)) & 0x1

bool __asan_checkrange(void* ptr, size_t sz) {
   bool okay = true;
   if (ptr >= asan_heap_mem && ptr <= asan_shadow) {
      for (int i = 0; i < sz; i++) {
         unsigned char* shadow = MEM_TO_SHADOW(ptr + i);
         bool valid = GET_SHADOW(shadow, ptr + i);
         if (!valid) okay = false;
      }
   }
   return okay;
}

void __asan_doreport(void* ptr, void* caller, const char* type); //@ bottom of file


#define ASAN_GENFUNC(type, num) void __asan_##type##num##_noabort(void* ptr) { \
   if (!asan_ready) return; \
   bool valid = __asan_checkrange(ptr, num); \
   if (!valid) __asan_doreport(ptr, __builtin_return_address(0), #type); \
}

ASAN_GENFUNC(load, 1);
ASAN_GENFUNC(store, 1);
ASAN_GENFUNC(load, 2);
ASAN_GENFUNC(store, 2);
ASAN_GENFUNC(load, 4);
ASAN_GENFUNC(store, 4);
ASAN_GENFUNC(load, 8);
ASAN_GENFUNC(store, 8);
ASAN_GENFUNC(load, 16);
ASAN_GENFUNC(store, 16);

void __asan_loadN_noabort(void* ptr, unsigned int size) {
   if (!asan_ready) return;
   bool valid = __asan_checkrange(ptr, (size_t)size);
   if (!valid) __asan_doreport(ptr, __builtin_return_address(0), "multiple load");
}

void __asan_storeN_noabort(void* ptr, unsigned int size) {
   if (!asan_ready) return;
   bool valid = __asan_checkrange(ptr, (size_t)size);
   if (!valid) __asan_doreport(ptr, __builtin_return_address(0), "multiple store");
}

void __asan_handle_no_return() {
   //We only do heap checking, so no need to fiddle here
}

void memoryInitialize(void)
{
    for (int i = 0; i < LSAN_ALLOCS_SZ; i++) {
       lsan_allocs[i].allocated = false;
    }
    net_print("[LSAN] LSAN initialized\n");

    MEMHeapHandle mem2_heap_handle = MEMGetBaseHeapHandle(MEM_BASE_HEAP_MEM2);
    unsigned int mem2_alloc_sz = MEMGetAllocatableSizeForExpHeapEx(mem2_heap_handle, 4);
    asan_sz = (mem2_alloc_sz / 4) & ~0x3;

    asan_heap_mem = MEMAllocFromExpHeapEx(mem2_heap_handle, asan_sz * 2, 4);

    asan_heap = MEMCreateExpHeapEx(asan_heap_mem, asan_sz, 0);
    unsigned int asan_heap_sz = MEMGetAllocatableSizeForExpHeapEx(asan_heap, 4);

    char buf[255];
    __os_snprintf(buf, 255, "[ASAN] Allocated wrapheap at %08X, size %08X. Avail RAM is %08X.\n", asan_heap, asan_sz, asan_heap_sz);
    net_print(buf);

    asan_shadow = (void*)(((unsigned int)asan_heap_mem) + asan_sz);
    asan_shadow_off = (unsigned int)asan_heap - (unsigned int)asan_shadow;

    memset(asan_shadow, 0, asan_sz);

    __os_snprintf(buf, 255, "[ASAN] Shadow at %08X. Final shadow address at %08X, final alloced at %08X\n", asan_shadow, asan_shadow + asan_sz, asan_heap_mem + (asan_sz * 2));
    net_print(buf);

    asan_ready = true;

    MEMHeapHandle mem1_heap_handle = MEMGetBaseHeapHandle(MEM_BASE_HEAP_MEM1);
    unsigned int mem1_allocatable_size = MEMGetAllocatableSizeForFrmHeapEx(mem1_heap_handle, 4);
    void *mem1_memory = MEMAllocFromFrmHeapEx(mem1_heap_handle, mem1_allocatable_size, 4);
    if(mem1_memory)
        mem1_heap = MEMCreateExpHeapEx(mem1_memory, mem1_allocatable_size, 0);

    MEMHeapHandle bucket_heap_handle = MEMGetBaseHeapHandle(MEM_BASE_HEAP_FG);
    unsigned int bucket_allocatable_size = MEMGetAllocatableSizeForFrmHeapEx(bucket_heap_handle, 4);
    void *bucket_memory = MEMAllocFromFrmHeapEx(bucket_heap_handle, bucket_allocatable_size, 4);
    if(bucket_memory)
        bucket_heap = MEMCreateExpHeapEx(bucket_memory, bucket_allocatable_size, 0);
}

void memoryRelease(void)
{
    for (int i = 0; i < LSAN_ALLOCS_SZ; i++) {
        if (lsan_allocs[i].allocated) {
           char buf[255];
           __os_snprintf(buf, 255, "[LSAN] Memory leak: %08X bytes at %08X; owner %08X\n", lsan_allocs[i].size, lsan_allocs[i].addr, lsan_allocs[i].owner);
           net_print(buf);
           break;
        }
    }

    asan_ready = false;
    MEMDestroyExpHeap(asan_heap);
    MEMFreeToExpHeap(MEMGetBaseHeapHandle(MEM_BASE_HEAP_MEM2), asan_heap_mem);
    asan_heap = NULL;
    asan_heap_mem = NULL;

    MEMDestroyExpHeap(mem1_heap);
    MEMFreeToFrmHeap(MEMGetBaseHeapHandle(MEM_BASE_HEAP_MEM1), MEM_FRAME_HEAP_FREE_ALL);
    mem1_heap = NULL;

    MEMDestroyExpHeap(bucket_heap);
    MEMFreeToFrmHeap(MEMGetBaseHeapHandle(MEM_BASE_HEAP_FG), MEM_FRAME_HEAP_FREE_ALL);
    bucket_heap = NULL;
}

void* _memalign_r(struct _reent *r, size_t alignment, size_t size)
{
   void* ptr = MEMAllocFromExpHeapEx(asan_heap, size, alignment);

   if (!ptr) return 0;

   bool lsan_ok = false;
   for (int i = 0; i < LSAN_ALLOCS_SZ; i++) {
      if (!lsan_allocs[i].allocated) {
         lsan_allocs[i].allocated = true;
         lsan_allocs[i].addr = ptr;
         lsan_allocs[i].size = size;
         lsan_allocs[i].owner = __builtin_return_address(0);
         lsan_ok = true;
         /*char buf[255];
         __os_snprintf(buf, 255, "[LSAN] Saved alloc %08X, sz %08X\n", ptr, size);
         net_print(buf);*/
         break;
      }
   }

   if (!lsan_ok) {
      net_print("[A/LSAN] WARNING: Too many allocs!\n");
   } else {
   /* Add to ASAN */
      for (size_t i = 0; i < size; i++) {
         SET_SHADOW(MEM_TO_SHADOW(ptr + i), ptr + i);
      }
   }

   return ptr;
}

void* _malloc_r(struct _reent *r, size_t size)
{
   return _memalign_r(r, 4, size);
}

void _free_r(struct _reent *r, void *ptr)
{
   if (ptr) {
      size_t sz = 0;

      bool lsan_ok = false;
      for (int i = 0; i < LSAN_ALLOCS_SZ; i++) {
         if (lsan_allocs[i].allocated && lsan_allocs[i].addr == ptr) {
            lsan_allocs[i].allocated = false;
            sz = lsan_allocs[i].size; //Thanks, LSAN!
            lsan_ok = true;
            /*char buf[255];
            __os_snprintf(buf, 255, "[LSAN] Freed %08X, sz %08X\n", lsan_allocs[i].addr, lsan_allocs[i].size);
            net_print(buf);*/
            break;
         }
      }

      if (!lsan_ok) {
         char buf[255];
         __os_snprintf(buf, 255, "[LSAN] WARNING: attempted free %08X; not in table!\n", ptr);
         net_print(buf);
         return;
      }

      for (size_t i = 0; i < sz; i++) {
         CLR_SHADOW(MEM_TO_SHADOW(ptr + i), ptr + i);
      }

      MEMFreeToExpHeap(asan_heap, ptr);
   }
}

size_t _malloc_usable_size_r(struct _reent *r, void *ptr)
{
   return MEMGetSizeForMBlockExpHeap(ptr);
}

void * _realloc_r(struct _reent *r, void *ptr, size_t size)
{
   if (!ptr)
      return _malloc_r(r, size);

   if (_malloc_usable_size_r(r, ptr) >= size)
      return ptr;

   void *realloc_ptr = _malloc_r(r, size);

   if(!realloc_ptr)
      return NULL;

   memcpy(realloc_ptr, ptr, _malloc_usable_size_r(r, ptr));
   _free_r(r, ptr);

   return realloc_ptr;
}

void* _calloc_r(struct _reent *r, size_t num, size_t size)
{
   void *ptr = _malloc_r(r, num*size);

   if(ptr) {
      memset(ptr, 0, num*size);
   }

   return ptr;
}

void * _valloc_r(struct _reent *r, size_t size)
{
   return _memalign_r(r, 64, size);
}


//!-------------------------------------------------------------------------------------------
//! some wrappers
//!-------------------------------------------------------------------------------------------
void * MEM2_alloc(unsigned int size, unsigned int align)
{
    return _memalign_r(NULL, align, size);
    //return MEMAllocFromExpHeapEx(MEMGetBaseHeapHandle(MEM_BASE_HEAP_MEM2), size, align);
}

void MEM2_free(void *ptr)
{
   if (ptr)
      _free_r(NULL, ptr);
      //MEMFreeToExpHeap(MEMGetBaseHeapHandle(MEM_BASE_HEAP_MEM2), ptr);
}

void * MEM1_alloc(unsigned int size, unsigned int align)
{
    if (align < 4)
        align = 4;
    return MEMAllocFromExpHeapEx(mem1_heap, size, align);
}

void MEM1_free(void *ptr)
{
    MEMFreeToExpHeap(mem1_heap, ptr);
}

void * MEMBucket_alloc(unsigned int size, unsigned int align)
{
    if (align < 4)
        align = 4;
    return MEMAllocFromExpHeapEx(bucket_heap, size, align);
}

void MEMBucket_free(void *ptr)
{
    MEMFreeToExpHeap(bucket_heap, ptr);
}

typedef struct _framerec
{
   struct _framerec* up;
   void* lr;
} frame_rec, *frame_rec_t;

extern unsigned int __code_start;
#define TEXT_START (void*)&__code_start
extern unsigned int __code_end;
#define TEXT_END (void*)&__code_end

#define buf_add(fmt, ...) cur_buf += __os_snprintf(cur_buf, 2047 - (buf - cur_buf), fmt, __VA_ARGS__)

void __asan_doreport(void* ptr, void* caller, const char* type) {
   char buf[2048];
   char* cur_buf = buf;
   buf_add("======================== ASAN: out-of-bounds %s\n", type);

   if (caller >= TEXT_START && caller < TEXT_END) {
      char symbolName[64];
		OSGetSymbolName((unsigned int)caller, symbolName, 63);
      //don't want library name today
      char* name = strchr(symbolName, '|') + sizeof(char);

      buf_add("Source: %08X(%08X):%s\n", caller, caller - TEXT_START, name);
   } else {
      buf_add("Source: %08X(        ):<unknown>\n", caller);
   }

   //Thanks, LSAN!
   int closest_over = -1, closest_under = -1, uaf = -1;
   for (int i = 0; i < LSAN_ALLOCS_SZ; i++) {
   /* Candidate for closest if we are an overflow */
      if (lsan_allocs[i].allocated && ptr > lsan_allocs[i].addr + lsan_allocs[i].size) {
         if (closest_over == -1) {
            closest_over = i;
      /* If this allocation is closer than the one in closest_over, update */
         } else if (ptr - (lsan_allocs[i].addr + lsan_allocs[i].size) < ptr - (lsan_allocs[closest_over].addr + lsan_allocs[closest_over].size)) {
            closest_over = i;
         }
   /* Candidate for under */
      } else if (lsan_allocs[i].allocated && ptr < lsan_allocs[i].addr) {
         if (closest_under == -1) {
            closest_under = i;
         } else if (lsan_allocs[i].addr - ptr < lsan_allocs[closest_under].addr - ptr) {
            closest_under = i;
         }
      } else if (!lsan_allocs[i].allocated && ptr > lsan_allocs[i].addr && ptr < lsan_allocs[i].addr + lsan_allocs[i].size) {
         if (uaf == -1) {
            uaf = i;
         }
      }
   }

   buf_add("Bad %s was on address %08X. Guessing possible issues:\n", type, ptr);

   buf_add("Guess     Chunk    ChunkSz  Dist     ChunkOwner\n", 0);
   if (closest_over >= 0) {
      char symbolName[64];
		OSGetSymbolName((unsigned int)lsan_allocs[closest_over].owner, symbolName, 63);
      char* name = strchr(symbolName, '|') + sizeof(char);

      buf_add("Overflow  %08X %08X %08X %s\n", lsan_allocs[closest_over].addr, lsan_allocs[closest_over].size, ptr - (lsan_allocs[closest_over].addr + lsan_allocs[closest_over].size), name);
   }
   if (closest_under >= 0) {
      char symbolName[64];
		OSGetSymbolName((unsigned int)lsan_allocs[closest_under].owner, symbolName, 63);
      char* name = strchr(symbolName, '|') + sizeof(char);

      buf_add("Underflow %08X %08X %08X %s\n", lsan_allocs[closest_under].addr, lsan_allocs[closest_under].size, lsan_allocs[closest_under].addr - ptr, name);
   }
   if (uaf >= 0) {
      char symbolName[64];
      OSGetSymbolName((unsigned int)lsan_allocs[uaf].owner, symbolName, 63);
      char* name = strchr(symbolName, '|') + sizeof(char);

      buf_add("UaF       %08X %08X %08X %s\n", lsan_allocs[uaf].addr, lsan_allocs[uaf].size, ptr - lsan_allocs[uaf].addr, name);
   }

   net_print(buf);
}
