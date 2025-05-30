/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#ifndef ASMX86_H_
#define ASMX86_H_

#include <stdint.h>
#include <unistd.h>
#include "utils/bullseye.h"

#define __xg(x) ((volatile long *)(x))

#define mb()     asm volatile("" ::: "memory")
#define rmb()    mb()
#define wmb()    asm volatile("" ::: "memory")
#define wc_wmb() asm volatile("sfence" ::: "memory")

#define COPY_64B_NT(dst, src)                                                                      \
    __asm__ __volatile__(" movdqa   (%1),%%xmm0\n"                                                 \
                         " movdqa 16(%1),%%xmm1\n"                                                 \
                         " movdqa 32(%1),%%xmm2\n"                                                 \
                         " movdqa 48(%1),%%xmm3\n"                                                 \
                         " movntdq %%xmm0,   (%0)\n"                                               \
                         " movntdq %%xmm1, 16(%0)\n"                                               \
                         " movntdq %%xmm2, 32(%0)\n"                                               \
                         " movntdq %%xmm3, 48(%0)\n"                                               \
                         :                                                                         \
                         : "r"(dst), "r"(src)                                                      \
                         : "memory");                                                              \
    dst += 8;                                                                                      \
    src += 8

#if _BullseyeCoverage
#pragma BullseyeCoverage off
#endif
/**
 * Atomic swap
 */
static inline unsigned long xchg(unsigned long x, volatile void *ptr)
{
    __asm__ __volatile__("xchg %0,%1" : "=r"(x) : "m"(*__xg(ptr)), "0"(x) : "memory");
    return x;
}

/**
 * Atomic compare-and-swap
 */
static inline bool cmpxchg(unsigned long old_value, unsigned long new_value, volatile void *ptr)
{
    unsigned long prev_value = old_value;
    __asm__ __volatile__("lock; cmpxchg %1,%2"
                         : "=a"(prev_value)
                         : "r"(new_value), "m"(*__xg(ptr)), "0"(old_value)
                         : "memory");
    return prev_value == old_value;
}
#if _BullseyeCoverage
#pragma BullseyeCoverage on
#endif

/**
 * Add to the atomic variable.
 * @param i integer value to add.
 * @param v pointer of type atomic_t.
 * @return Value before add.
 */
static inline int atomic_fetch_and_add(int x, volatile int *ptr)
{
    __asm__ __volatile__("lock; xaddl %0,%1" : "=r"(x) : "m"(*ptr), "0"(x) : "memory");
    return x;
}

/**
 * Add to the atomic variable. Relaxed memory order.
 * @param i integer value to add.
 * @param v pointer of type atomic_t.
 * @return Value before add.
 */
static inline int atomic_fetch_and_add_relaxed(int x, volatile int *ptr)
{
    return atomic_fetch_and_add(x, ptr);
}

/**
 * Read RDTSC register
 */
static inline void gettimeoftsc(unsigned long long *p_tscval)
{
    uint32_t upper_32, lower_32;

    // ReaD Time Stamp Counter (RDTCS)
    __asm__ __volatile__("rdtsc" : "=a"(lower_32), "=d"(upper_32));

    // Copy to user
    *p_tscval = (((unsigned long long)upper_32) << 32) | lower_32;
}

/**
 * Cache Line Prefetch - Arch specific!
 */
#ifndef L1_CACHE_BYTES
#define L1_CACHE_BYTES 64
#endif

static inline void prefetch(void *x)
{
#if defined __i386__ || defined __x86_64__
    asm volatile("prefetcht0 %0" ::"m"(*(unsigned long *)x));
#else
    {
        // Use simple memcpy to get data into cache
        char temp_prefetch_block[L1_CACHE_BYTES];
        memcpy(temp_prefetch_block, x, L1_CACHE_BYTES);
    }
#endif
}

static inline void prefetch_range(void *addr, size_t len)
{
    char *cp = (char *)addr;
    char *end = (char *)addr + len;
    for (; cp < end; cp += L1_CACHE_BYTES) {
        prefetch(cp);
    }
}

#endif
