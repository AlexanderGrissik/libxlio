/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#ifndef TOOLS_DAEMON_DAEMON_H_
#define TOOLS_DAEMON_DAEMON_H_

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>
#include <ctype.h>
#include <unistd.h>
#include <stdint.h>
#include <errno.h>
#include <signal.h>
#include <fcntl.h>
#include <time.h>
#include <assert.h>
#include <stdarg.h>
#include <syslog.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <arpa/inet.h>
#include <net/if.h>
#include <sys/time.h>
#include <ifaddrs.h>

#ifdef HAVE_LINUX_LIMITS_H
#include <linux/limits.h>
#endif

#include <netinet/ip.h> /* for struct iphdr */
#include <netinet/ip6.h> /* for struct ip6_hdr */
#include <netinet/tcp.h>

#include "core/util/agent_def.h"
#include "core/util/list.h"
#include "utils/clock.h"

#define MODULE_NAME "xliod"

#define EXIT_SUCCESS 0
#define EXIT_FAILURE 1

#ifndef NOT_IN_USE
#define NOT_IN_USE(P) ((void)(P))
#endif

#define INVALID_VALUE     (-1)
#define STATE_ESTABLISHED 4

#define PID_MAX                                                                                    \
    499 /**< Default maximum number of processes                                                   \
             per node (should be prime number) */
#define FID_MAX                                                                                    \
    65599 /**< Default maximum number of sockets                                                   \
               per process (should be prime number) */

#ifndef HAVE_LINUX_LIMITS_H
#define NAME_MAX 255 /**< chars in a file name */
#define PATH_MAX 4096 /**< chars in a path name including null */
#endif

#define log_fatal(fmt, ...)                                                                        \
    do {                                                                                           \
        if (daemon_cfg.opt.log_level > 0)                                                          \
            sys_log(LOG_ALERT, "[FATAL ] " fmt, ##__VA_ARGS__);                                    \
    } while (0)

#define log_error(fmt, ...)                                                                        \
    do {                                                                                           \
        if (daemon_cfg.opt.log_level > 1)                                                          \
            sys_log(LOG_ERR, "[ERROR ] " fmt, ##__VA_ARGS__);                                      \
    } while (0)

#define log_warn(fmt, ...)                                                                         \
    do {                                                                                           \
        if (daemon_cfg.opt.log_level > 2)                                                          \
            sys_log(LOG_WARNING, "[WARN  ] " fmt, ##__VA_ARGS__);                                  \
    } while (0)

#define log_info(fmt, ...)                                                                         \
    do {                                                                                           \
        if (daemon_cfg.opt.log_level > 3)                                                          \
            sys_log(LOG_NOTICE, "[INFO  ] " fmt, ##__VA_ARGS__);                                   \
    } while (0)

#define log_debug(fmt, ...)                                                                        \
    do {                                                                                           \
        if (daemon_cfg.opt.log_level > 4)                                                          \
            sys_log(LOG_INFO, "[DEBUG ] " fmt, ##__VA_ARGS__);                                     \
    } while (0)

#define log_trace(fmt, ...)                                                                        \
    do {                                                                                           \
        if (daemon_cfg.opt.log_level > 5)                                                          \
            sys_log(LOG_INFO, "[TRACE ] " fmt, ##__VA_ARGS__);                                     \
    } while (0)

#define log_hexdump(_ptr, _size)                                                                   \
    do {                                                                                           \
        if (daemon_cfg.opt.log_level > 5)                                                          \
            sys_hexdump((_ptr), (_size));                                                          \
    } while (0)

/**
 * @struct module_cfg
 * @brief Configuration parameters in global values
 */
struct module_cfg {
    struct {
        int mode; /**< 0 - daemon, 1 - console */
        int log_level; /**< 0..5 verbose level */
        int max_pid_num; /**< maximum number of processes per node */
        int max_fid_num; /**< maximum number of sockets per process */
        int force_rst; /**< RST method
                        * 0 - only system RST is sent as
                        * reaction on spoofed SYN
                        * 1 - form and send internal RST
                        * based on SeqNo */
        int retry_interval; /**< daemon time interval between spoofed SYN packets */
    } opt;
    volatile sig_atomic_t sig;
    const char *lock_file;
    int lock_fd;
    const char *sock_file;
    int sock_fd;
    int raw_fd_ip4;
    int raw_fd_ip6;
    int notify_fd;
    const char *notify_dir;
    hash_t ht;
    tc_t tc;
    struct list_head if_list;
};

extern struct module_cfg daemon_cfg;

/**
 * @struct sockaddr_store
 * @brief Describe socket address ipv4/ipv6
 */
struct sockaddr_store {
    union {
        sa_family_t family;
        struct sockaddr_in addr4;
        struct sockaddr_in6 addr6;
    };
};

/**
 * @struct store_pid
 * @brief Describe process using pid as unique key
 */
struct store_pid {
    pid_t pid; /**< Process id */
    hash_t ht; /**< Handle to socket store */
    struct list_head flow_list; /**< List of flows */
    uint32_t lib_ver; /**< Library version that the process uses */
    struct timeval t_start; /**< Start time of the process */
};

/**
 * @struct store_fid
 * @brief Describe socket using fid as unique key
 */
struct store_fid {
    int fid; /**< Socket id */
    struct sockaddr_store src; /**< Source address */
    struct sockaddr_store dst; /**< Destination address */
    uint8_t type; /**< Connection type */
    uint8_t state; /**< Current TCP state of the connection */
};

/**
 * @struct store_flow
 * @brief Describe flow
 */
struct store_flow {
    struct list_head item; /**< Link to use in queue */
    uint32_t handle; /**< Handle value in term of tc */
    int type; /**< Flow type */
    uint32_t if_id; /**< Interface index */
    uint32_t tap_id; /**< Tap device index */
    struct {
        struct sockaddr_store src; /**< Source address */
        struct sockaddr_store dst; /**< Destination address */
    } flow;
};

void sys_log(int level, const char *format, ...);

ssize_t sys_sendto(int sockfd, const void *buf, size_t len, int flags,
                   const struct sockaddr *dest_addr, socklen_t addrlen);

char *sys_exec(const char *format, ...);

static inline char *sys_addr2str(struct sockaddr_store *addr)
{
    static char buf[100];
    static __thread char addrbuf[sizeof(buf) + sizeof(uint16_t) + 5];
    if (addr->family == AF_INET) {
        inet_ntop(addr->family, &addr->addr4.sin_addr, buf, sizeof(buf) - 1);
        sprintf(addrbuf, "%s:%d", buf, ntohs(addr->addr4.sin_port));
    } else {
        inet_ntop(addr->family, &addr->addr6.sin6_addr, buf, sizeof(buf) - 1);
        sprintf(addrbuf, "%s:%d", buf, ntohs(addr->addr6.sin6_port));
    }

    return addrbuf;
}

static inline char *sys_ip2str(struct sockaddr_store *addr)
{
    static __thread char ipbuf[100];
    if (addr->family == AF_INET) {
        inet_ntop(addr->family, &addr->addr4.sin_addr, ipbuf, sizeof(ipbuf) - 1);
    } else {
        inet_ntop(addr->family, &addr->addr6.sin6_addr, ipbuf, sizeof(ipbuf) - 1);
    }

    return ipbuf;
}

static inline uint32_t sys_lo_ifindex(void)
{
    static __thread uint32_t lo_ifindex = 0;
    struct ifaddrs *ifaddr, *ifa;

    if (lo_ifindex > 0) {
        return lo_ifindex;
    }

    if (!getifaddrs(&ifaddr)) {
        for (ifa = ifaddr; NULL != ifa; ifa = ifa->ifa_next) {
            if (ifa->ifa_addr->sa_family == AF_INET && (ifa->ifa_flags & IFF_LOOPBACK)) {
                lo_ifindex = if_nametoindex(ifa->ifa_name);
                break;
            }
        }
        freeifaddrs(ifaddr);
    }

    return lo_ifindex;
}

static inline char *sys_lo_ifname(void)
{
    static __thread char lo_ifname[IF_NAMESIZE] = {0};

    if (lo_ifname[0] > 0) {
        return lo_ifname;
    }

    if (NULL == if_indextoname(sys_lo_ifindex(), lo_ifname)) {
        lo_ifname[0] = 0;
    }

    return lo_ifname;
}

static inline int sys_iplocal(uint32_t addr)
{
    int rc = 0;
    struct ifaddrs *ifaddr, *ifa;
    struct sockaddr_in *sa;

    if (!getifaddrs(&ifaddr)) {
        for (ifa = ifaddr; NULL != ifa; ifa = ifa->ifa_next) {
            if (ifa->ifa_addr->sa_family == AF_INET) {
                sa = (struct sockaddr_in *)ifa->ifa_addr;
                if (addr == sa->sin_addr.s_addr) {
                    rc = 1;
                    break;
                }
            }
        }
        freeifaddrs(ifaddr);
    }

    return rc;
}

static inline void sys_hexdump(void *ptr, int buflen)
{
    unsigned char *buf = (unsigned char *)ptr;
    char out_buf[256];
    int ret = 0;
    int out_pos = 0;
    int i, j;

    log_trace("dump data at %p\n", ptr);
    for (i = 0; i < buflen; i += 16) {
        out_pos = 0;
        ret = sprintf(out_buf + out_pos, "%06x: ", i);
        if (ret < 0) {
            return;
        }
        out_pos += ret;
        for (j = 0; j < 16; j++) {
            if (i + j < buflen) {
                ret = sprintf(out_buf + out_pos, "%02x ", buf[i + j]);
            } else {
                ret = sprintf(out_buf + out_pos, "   ");
            }
            if (ret < 0) {
                return;
            }
            out_pos += ret;
        }
        ret = sprintf(out_buf + out_pos, " ");
        if (ret < 0) {
            return;
        }
        out_pos += ret;
        for (j = 0; j < 16; j++) {
            if (i + j < buflen) {
                ret = sprintf(out_buf + out_pos, "%c", isprint(buf[i + j]) ? buf[i + j] : '.');
                if (ret < 0) {
                    return;
                }
                out_pos += ret;
            }
        }
        ret = sprintf(out_buf + out_pos, "\n");
        if (ret < 0) {
            return;
        }
        log_trace("%s", out_buf);
    }
}

#endif /* TOOLS_DAEMON_DAEMON_H_ */
