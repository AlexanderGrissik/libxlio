/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#ifndef TESTS_GTEST_COMMON_DEF_H_
#define TESTS_GTEST_COMMON_DEF_H_

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <stdint.h>
#define __STDC_FORMAT_MACROS
#include <inttypes.h> /* printf PRItn */
#include <unistd.h>
#include <sys/time.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/epoll.h>
#include <sys/select.h>
#include <sys/wait.h> // WIFEXITED, etc.
#include <sys/eventfd.h>
#include <sys/prctl.h> // prctl(), PR_SET_PDEATHSIG
#include <sys/sendfile.h>
#include <netdb.h>
#include <netinet/in.h>
#include <netinet/ip.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#include <net/if.h>
#include <ifaddrs.h>
#include <pthread.h>
#include <inttypes.h> /* printf PRItn */
#include <fcntl.h>
#include <poll.h>
#include <ctype.h>
#include <malloc.h>
#include <math.h>
#include <complex.h>
#include <time.h>
#include <signal.h>

#include "googletest/include/gtest/gtest.h"

#include "config.h"

#define INLINE __inline

#ifndef UNREFERENCED_PARAMETER
#define UNREFERENCED_PARAMETER(P) ((void)P)
#endif

#define QUOTE(name) #name
#define STR(macro)  QUOTE(macro)

#define ARRAY_SIZE(a) (sizeof(a) / sizeof(a[0]))

/* Platform specific 16-byte alignment macro switch.
   On Visual C++ it would substitute __declspec(align(16)).
   On GCC it substitutes __attribute__((aligned (16))).
*/

#if defined(_MSC_VER)
#define ALIGN(x) __declspec(align(x))
#else
#define ALIGN(x) __attribute__((aligned(x)))
#endif

#if !defined(EOK)
#define EOK 0 /* no error */
#endif

#define CHECK_ERR_OK(rc)                                                                           \
    EXPECT_EQ(0, (rc));                                                                            \
    if ((rc) < 0) {                                                                                \
        ASSERT_EQ(EOK, errno);                                                                     \
    }

#ifndef container_of
/**
 * container_of - cast a member of a structure out to the containing structure
 * @ptr:        the pointer to the member.
 * @type:       the type of the container struct this is embedded in.
 * @member:     the name of the member within the struct.
 *
 */
#define container_of(ptr, type, member) (type *)((char *)(ptr)-offsetof(type, member))
#endif

#define UNDEFINED_VALUE (-1)

typedef union {
    struct sockaddr addr;
    struct sockaddr_in addr4;
    struct sockaddr_in6 addr6;
} sockaddr_store_t;

struct gtest_configure_t {
    int log_level;
    int random_seed;
    sockaddr_store_t client_addr;
    sockaddr_store_t server_addr;
    sockaddr_store_t remote_addr;
    uint16_t port;
    bool def_gw_exists;
};

#endif /* TESTS_GTEST_COMMON_DEF_H_ */
