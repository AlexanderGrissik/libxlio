/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <sys/time.h>
#include <sys/socket.h>
#include <sys/un.h>

#include "core/lwip/tcp.h" /* display TCP states */
#include "hash.h"
#include "tc.h"
#include "daemon.h"

int open_message(void);
void close_message(void);
int proc_message(void);

extern int add_flow(struct store_pid *pid_value, struct store_flow *value);
extern int del_flow(struct store_pid *pid_value, struct store_flow *value);

static int proc_msg_init(struct xlio_hdr *msg_hdr, size_t size, struct sockaddr_un *peeraddr);
static int proc_msg_exit(struct xlio_hdr *msg_hdr, size_t size);
static int proc_msg_state(struct xlio_hdr *msg_hdr, size_t size);
static int proc_msg_flow(struct xlio_hdr *msg_hdr, size_t size, struct sockaddr_un *peeraddr);

int open_message(void)
{
    int rc = 0;
    int optval = 1;
    struct sockaddr_un server_addr;

    /* Create UNIX UDP socket to receive data from XLIO processes */
    memset(&server_addr, 0, sizeof(server_addr));
    server_addr.sun_family = AF_UNIX;
    strncpy(server_addr.sun_path, daemon_cfg.sock_file, sizeof(server_addr.sun_path) - 1);
    /* remove possible old socket */
    unlink(daemon_cfg.sock_file);

    if ((daemon_cfg.sock_fd = socket(AF_UNIX, SOCK_DGRAM, 0)) < 0) {
        log_error("Failed to call socket() errno %d (%s)\n", errno, strerror(errno));
        rc = -errno;
        goto err;
    }

    optval = 1;
    rc = setsockopt(daemon_cfg.sock_fd, SOL_SOCKET, SO_REUSEADDR, &optval, sizeof(optval));
    if (rc < 0) {
        log_error("Failed to call setsockopt() errno %d (%s)\n", errno, strerror(errno));
        rc = -errno;
        goto err;
    }

    /* bind created socket */
    if (bind(daemon_cfg.sock_fd, (struct sockaddr *)&server_addr, sizeof(server_addr)) < 0) {
        log_error("Failed to call bind() errno %d (%s)\n", errno, strerror(errno));
        rc = -errno;
        goto err;
    }

    /* Make the socket non-blocking */
    optval = fcntl(daemon_cfg.sock_fd, F_GETFL);
    if (optval < 0) {
        rc = -errno;
        log_error("Failed to get socket flags errno %d (%s)\n", errno, strerror(errno));
        goto err;
    }
    optval |= O_NONBLOCK;
    rc = fcntl(daemon_cfg.sock_fd, F_SETFL, optval);
    if (rc < 0) {
        rc = -errno;
        log_error("Failed to set socket flags errno %d (%s)\n", errno, strerror(errno));
        goto err;
    }

err:
    return rc;
}

void close_message(void)
{
    if (daemon_cfg.sock_fd > 0) {
        close(daemon_cfg.sock_fd);
    }
    unlink(daemon_cfg.sock_file);
}

int proc_message(void)
{
    int rc = 0;
    struct sockaddr_un peeraddr;
    socklen_t addrlen = sizeof(peeraddr);
    char msg_recv[4096];
    int len = 0;
    struct xlio_hdr *msg_hdr = NULL;

again:
    len = recvfrom(daemon_cfg.sock_fd, &msg_recv, sizeof(msg_recv), 0, (struct sockaddr *)&peeraddr,
                   &addrlen);
    if (len < 0) {
        if (errno == EINTR) {
            goto again;
        }
        rc = -errno;
        log_error("Failed recvfrom() errno %d (%s)\n", errno, strerror(errno));
        goto err;
    }

    /* Parse and process messages */
    while (len > 0) {
        if (len < (int)sizeof(struct xlio_hdr)) {
            rc = -EBADMSG;
            log_error("Invalid message lenght from %s as %d errno %d (%s)\n",
                      (addrlen > 0 ? peeraddr.sun_path : "n/a"), len, errno, strerror(errno));
            goto err;
        }
        msg_hdr = (struct xlio_hdr *)&msg_recv;
        log_debug("getting message ([%d] ver: %d pid: %d)\n", msg_hdr->code, msg_hdr->ver,
                  msg_hdr->pid);

        switch (msg_hdr->code) {
        case XLIO_MSG_INIT:
            rc = proc_msg_init(msg_hdr, len, &peeraddr);
            break;
        case XLIO_MSG_STATE:
            rc = proc_msg_state(msg_hdr, len);
            break;
        case XLIO_MSG_EXIT:
            rc = proc_msg_exit(msg_hdr, len);
            break;
        case XLIO_MSG_FLOW:
            /* Note: special loopback logic, it
             * should be added first as far as observed issue with delay
             * in activation loopback filters in case two processes
             * communicate locally w/o SRIOV
             */
            proc_msg_flow(msg_hdr, len, NULL);
            rc = proc_msg_flow(msg_hdr, len, &peeraddr);
            break;
        default:
            rc = -EPROTO;
            log_error("Received unknown message errno %d (%s)\n", errno, strerror(errno));
            goto err;
        }
        if (0 < rc) {
            len -= rc;
            rc = 0;
        } else {
            goto err;
        }
    }

err:
    return rc;
}

static int proc_msg_init(struct xlio_hdr *msg_hdr, size_t size, struct sockaddr_un *peeraddr)
{
    struct xlio_msg_init *data;
    struct store_pid *value;
    size_t err = 0;

    assert(msg_hdr);
    assert(msg_hdr->code == XLIO_MSG_INIT);
    assert(size);

    data = (struct xlio_msg_init *)msg_hdr;
    if (size < sizeof(*data)) {
        return -EBADMSG;
    }

    /* Message protocol version check */
    if (data->hdr.ver > XLIO_AGENT_VER) {
        log_error("Protocol message mismatch (XLIO_AGENT_VER = %d) errno %d (%s)\n", XLIO_AGENT_VER,
                  errno, strerror(errno));
        err = -EBADMSG;
        goto send_response;
    }

    /* Allocate memory for this value in this place
     * Free this memory during hash_del() call or hash_destroy()
     */
    value = (void *)calloc(1, sizeof(*value));
    if (NULL == value) {
        return -ENOMEM;
    }

    value->pid = data->hdr.pid;
    value->lib_ver = data->ver;
    gettimeofday(&value->t_start, NULL);
    INIT_LIST_HEAD(&value->flow_list);

    value->ht = hash_create(&free, daemon_cfg.opt.max_fid_num);
    if (NULL == value->ht) {
        log_error("Failed hash_create() for %d entries errno %d (%s)\n", daemon_cfg.opt.max_fid_num,
                  errno, strerror(errno));
        free(value);
        return -EFAULT;
    }

    if (hash_put(daemon_cfg.ht, value->pid, value) != value) {
        log_error("Failed hash_put() count: %d size: %d errno %d (%s)\n", hash_count(daemon_cfg.ht),
                  hash_size(daemon_cfg.ht), errno, strerror(errno));
        hash_destroy(value->ht);
        free(value);
        return -EFAULT;
    }

    log_debug("[%d] put into the storage\n", data->hdr.pid);

send_response:
    data->hdr.code |= XLIO_MSG_ACK;
    data->hdr.ver = XLIO_AGENT_VER;
    if (0 > sys_sendto(daemon_cfg.sock_fd, data, sizeof(*data), 0, (struct sockaddr *)peeraddr,
                       sizeof(*peeraddr))) {
        log_warn("Failed sendto() message errno %d (%s)\n", errno, strerror(errno));
    }

    return err ? err : (sizeof(*data));
}

static int proc_msg_exit(struct xlio_hdr *msg_hdr, size_t size)
{
    struct xlio_msg_exit *data;
    struct store_pid *pid_value = NULL;

    assert(msg_hdr);
    assert(msg_hdr->code == XLIO_MSG_EXIT);
    assert(size);

    data = (struct xlio_msg_exit *)msg_hdr;
    if (size < sizeof(*data)) {
        return -EBADMSG;
    }

    pid_value = hash_get(daemon_cfg.ht, data->hdr.pid);
    if (pid_value) {
        struct store_flow *flow_value = NULL;
        struct list_head *cur_entry = NULL;
        struct list_head *tmp_entry = NULL;
        list_for_each_safe(cur_entry, tmp_entry, &pid_value->flow_list)
        {
            flow_value = list_entry(cur_entry, struct store_flow, item);
            list_del_init(&flow_value->item);
            del_flow(pid_value, flow_value);
            free(flow_value);
        }

        hash_del(daemon_cfg.ht, pid_value->pid);
    }

    log_debug("[%d] remove from the storage\n", data->hdr.pid);

    return (sizeof(*data));
}

static int proc_msg_state(struct xlio_hdr *msg_hdr, size_t size)
{
    struct xlio_msg_state *data;
    struct store_pid *pid_value;
    struct store_fid *value;

    assert(msg_hdr);
    assert(msg_hdr->code == XLIO_MSG_STATE);
    assert(size);

    data = (struct xlio_msg_state *)msg_hdr;
    if (size < sizeof(*data)) {
        return -EBADMSG;
    }

    pid_value = hash_get(daemon_cfg.ht, data->hdr.pid);
    if (NULL == pid_value) {
        /* Return success because this case can be valid
         * if the process is terminated using abnormal way
         * So no needs in acknowledgement.
         */
        log_debug("Failed hash_get() for pid %d errno %d (%s). The process should be abnormal "
                  "terminated\n",
                  data->hdr.pid, errno, strerror(errno));
        return ((int)sizeof(*data));
    }

    /* Do not store information about closed socket
     * It is a protection for hypothetical scenario when number for new
     * sockets are incremented instead of using number
     * of closed sockets
     */
    if ((CLOSED == data->state) && (SOCK_STREAM == data->type)) {
        hash_del(pid_value->ht, data->fid);

        log_debug("[%d] remove fid: %d type: %d state: %s\n", data->hdr.pid, data->fid, data->type,
                  (data->state < (sizeof(tcp_state_str) / sizeof(tcp_state_str[0]))
                       ? tcp_state_str[data->state]
                       : "n/a"));
        return (sizeof(*data));
    }

    /* Allocate memory for this value in this place
     * Free this memory during hash_del() call or hash_destroy()
     */
    value = (void *)calloc(1, sizeof(*value));
    if (NULL == value) {
        return -ENOMEM;
    }

    value->fid = data->fid;
    value->type = data->type;
    value->state = data->state;
    value->src.family = data->src.family;
    if (value->src.family == AF_INET) {
        value->src.addr4.sin_port = data->src.port;
        value->src.addr4.sin_addr.s_addr = data->src.addr.ipv4;
    } else {
        value->src.addr6.sin6_port = data->src.port;
        memcpy(&value->src.addr6.sin6_addr.s6_addr[0], &data->src.addr.ipv6[0],
               sizeof(value->src.addr6.sin6_addr.s6_addr));
    }
    value->dst.family = data->dst.family;
    if (value->dst.family == AF_INET) {
        value->dst.addr4.sin_port = data->dst.port;
        value->dst.addr4.sin_addr.s_addr = data->dst.addr.ipv4;
    } else {
        value->dst.addr6.sin6_port = data->dst.port;
        memcpy(&value->dst.addr6.sin6_addr.s6_addr[0], &data->dst.addr.ipv6[0],
               sizeof(value->dst.addr6.sin6_addr.s6_addr));
    }

    if (hash_put(pid_value->ht, value->fid, value) != value) {
        log_error("Failed hash_put() count: %d size: %d errno %d (%s)\n", hash_count(pid_value->ht),
                  hash_size(pid_value->ht), errno, strerror(errno));
        free(value);
        return -EFAULT;
    }

    log_debug("[%d] update fid: %d type: %d state: %s\n", pid_value->pid, value->fid, value->type,
              (value->state < (sizeof(tcp_state_str) / sizeof(tcp_state_str[0]))
                   ? tcp_state_str[value->state]
                   : "n/a"));

    return (sizeof(*data));
}

static int proc_msg_flow(struct xlio_hdr *msg_hdr, size_t size, struct sockaddr_un *peeraddr)
{
    int rc = 0;
    struct xlio_msg_flow *data;
    struct store_pid *pid_value;
    struct store_flow *value = NULL;
    struct store_flow *cur_flow = NULL;
    struct list_head *cur_entry = NULL;
    int value_new = 0;
    int ack = 0;

    assert(msg_hdr);
    assert((msg_hdr->code & ~XLIO_MSG_ACK) == XLIO_MSG_FLOW);
    assert(size);

    data = (struct xlio_msg_flow *)msg_hdr;
    if (size < sizeof(*data)) {
        rc = -EBADMSG;
        goto err;
    }

    /* Note: special loopback logic */
    if (NULL == peeraddr && data->type == XLIO_MSG_FLOW_EGRESS) {
        return 0;
    }

    ack = (1 == data->hdr.status);

    pid_value = hash_get(daemon_cfg.ht, data->hdr.pid);
    if (NULL == pid_value) {
        /* Return success because this case can be valid
         * if the process is terminated using abnormal way
         * So no needs in acknowledgement.
         */
        log_debug("Failed hash_get() for pid %d errno %d (%s). The process should be abnormal "
                  "terminated\n",
                  data->hdr.pid, errno, strerror(errno));
        return ((int)sizeof(*data));
    }

    /* Allocate memory for this value in this place
     */
    value = (void *)calloc(1, sizeof(*value));
    if (NULL == value) {
        rc = -ENOMEM;
        goto err;
    }

    value->type = data->type;
    value->if_id = data->if_id;
    value->tap_id = data->tap_id;
    value->flow.dst.family = data->flow.dst.family;
    if (value->flow.dst.family == AF_INET) {
        value->flow.dst.addr4.sin_port = data->flow.dst.port;
        value->flow.dst.addr4.sin_addr.s_addr = data->flow.dst.addr.ipv4;
    } else {
        value->flow.dst.addr6.sin6_port = data->flow.dst.port;
        memcpy(&value->flow.dst.addr6.sin6_addr.s6_addr[0], &data->flow.dst.addr.ipv6[0],
               sizeof(value->flow.dst.addr6.sin6_addr.s6_addr));
    }

    switch (data->type) {
    case XLIO_MSG_FLOW_EGRESS:
    case XLIO_MSG_FLOW_TCP_3T:
    case XLIO_MSG_FLOW_UDP_3T:
        break;
    case XLIO_MSG_FLOW_TCP_5T:
    case XLIO_MSG_FLOW_UDP_5T:
        value->flow.src.family = data->flow.src.family;
        if (value->flow.src.family == AF_INET) {
            value->flow.src.addr4.sin_port = data->flow.src.port;
            value->flow.src.addr4.sin_addr.s_addr = data->flow.src.addr.ipv4;
        } else {
            value->flow.src.addr6.sin6_port = data->flow.src.port;
            memcpy(&value->flow.src.addr6.sin6_addr.s6_addr[0], &data->flow.src.addr.ipv6[0],
                   sizeof(value->flow.src.addr6.sin6_addr.s6_addr));
        }
        break;
    default:
        log_error("Received unknown message errno %d (%s)\n", errno, strerror(errno));
        rc = -EPROTO;
        goto err;
    }

    /* Note:
     * - special loopback logic when peeraddr is null
     * - avoid useless rules creation in case expected 5t traffic is local
     */
    if (NULL == peeraddr) {
        value->if_id = sys_lo_ifindex();
        ack = 0;
        if (value->if_id <= 0) {
            rc = -EFAULT;
            goto err;
        }
    } else if ((XLIO_MSG_FLOW_TCP_5T == data->type || XLIO_MSG_FLOW_UDP_5T == data->type) &&
               sys_iplocal(value->flow.src.addr4.sin_addr.s_addr)) {
        rc = 0;
        goto err;
    }

    if (XLIO_MSG_FLOW_ADD == data->action) {
        list_for_each(cur_entry, &pid_value->flow_list)
        {
            cur_flow = list_entry(cur_entry, struct store_flow, item);
            if (value->type == cur_flow->type && value->if_id == cur_flow->if_id &&
                value->tap_id == cur_flow->tap_id &&
                !memcmp(&value->flow, &cur_flow->flow, sizeof(cur_flow->flow))) {
                break;
            }
        }
        if (cur_entry == &pid_value->flow_list) {
            rc = add_flow(pid_value, value);
            if (rc < 0) {
                goto err;
            }
            value_new = 1; /* mark value as new to avoid releasing */
            list_add_tail(&value->item, &pid_value->flow_list);

            log_debug("[%d] add flow handle: 0x%08X type: %d if_id: %d tap_id: %d\n",
                      pid_value->pid, value->handle, value->type, value->if_id, value->tap_id);
        }
    }

    if (XLIO_MSG_FLOW_DEL == data->action) {
        list_for_each(cur_entry, &pid_value->flow_list)
        {
            cur_flow = list_entry(cur_entry, struct store_flow, item);
            if (value->type == cur_flow->type && value->if_id == cur_flow->if_id &&
                value->tap_id == cur_flow->tap_id &&
                !memcmp(&value->flow, &cur_flow->flow, sizeof(cur_flow->flow))) {
                log_debug("[%d] del flow handle: 0x%08X type: %d if_id: %d tap_id: %d\n",
                          pid_value->pid, cur_flow->handle, cur_flow->type, cur_flow->if_id,
                          cur_flow->tap_id);
                list_del_init(&cur_flow->item);
                rc = del_flow(pid_value, cur_flow);
                free(cur_flow);
                break;
            }
        }
    }

err:
    if (ack) {
        data->hdr.code |= XLIO_MSG_ACK;
        data->hdr.status = (rc ? 1 : 0);
        if (0 > sys_sendto(daemon_cfg.sock_fd, &data->hdr, sizeof(data->hdr), 0,
                           (struct sockaddr *)peeraddr, sizeof(*peeraddr))) {
            log_warn("Failed sendto() message errno %d (%s)\n", errno, strerror(errno));
        }
    }

    if (value && !value_new) {
        free(value);
    }

    return (rc ? rc : (int)sizeof(*data));
}
