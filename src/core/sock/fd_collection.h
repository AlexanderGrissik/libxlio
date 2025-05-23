/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#ifndef FD_COLLECTION_H
#define FD_COLLECTION_H

#include <stack>
#include <unordered_map>

#include "vlogger/vlogger.h"
#include "dev/ring_tap.h"
#include "event/event_handler_manager.h"
#include "event/timer_handler.h"
#include "sock/cleanable_obj.h"
#include "sock/sockinfo.h"
#include "iomux/epfd_info.h"
#include "utils/lock_wrapper.h"

typedef xlio_list_t<sockinfo, sockinfo::pending_to_remove_node_offset> sock_fd_api_list_t;
typedef xlio_list_t<epfd_info, epfd_info::epfd_info_node_offset> epfd_info_list_t;

typedef std::unordered_map<pthread_t, int> offload_thread_rule_t;

#if (MAX_DEFINED_LOG_LEVEL < DEFINED_VLOG_FINER)
#define fdcoll_logfuncall(log_fmt, log_args...) ((void)0)
#else
#define fdcoll_logfuncall(log_fmt, log_args...)                                                    \
    do {                                                                                           \
        if (g_vlogger_level >= VLOG_FUNC_ALL)                                                      \
            vlog_printf(VLOG_FUNC_ALL, "fdc:%d:%s() " log_fmt "\n", __LINE__, __FUNCTION__,        \
                        ##log_args);                                                               \
    } while (0)
#endif /* MAX_DEFINED_LOG_LEVEL */

extern global_stats_t g_global_stat_static;

class cq_channel_info : public cleanable_obj {
public:
    cq_channel_info(ring *p_ring)
        : m_p_ring(p_ring) {};
    ~cq_channel_info() override = default;
    ring *get_ring() const noexcept { return m_p_ring; };

protected:
    ring *m_p_ring;
};

class fd_collection : private lock_mutex_recursive {
public:
    fd_collection();
    ~fd_collection() override;

    /**
     * Create and add a sockinfo. Use get_sock() to get it.
     * @param domain e.g AF_INET.
     * @param type e.g SOCK_DGRAM.
     * @return socket fd or -1 on failure.
     */
    int addsocket(int fd, int domain, int type, bool check_offload = false);

    /**
     * Create epfd_info. Use get_epfd() to get it.
     * @param epfd epoll fd.
     * @param size epoll fd size (as passed to epoll_create).
     * @return 0 on success, -1 on failure.
     */
    int addepfd(int epfd, int size);

    /**
     * Create cq_channel_info. Use get_cq_channel_info() to get it.
     * @param cq_ch_fd: cq channel fd.
     * @param p_ring: pointer to ring which is the relevant rx_cq owner.
     * @return 0 on success, -1 on failure.
     */
    int add_cq_channel_fd(int cq_ch_fd, ring *p_ring);

    /**
     * Add tap fd index to tap_map.
     * @param tapfd: tap fd.
     * @param p_ring: pointer to ring owner of the tap.
     * @return 0 on success, -1 on failure.
     */
    int addtapfd(int tapfd, ring_tap *p_ring);

    /**
     * Remove sockinfo.
     */
    int del_sockfd(int fd, bool is_for_udp_pool = false);

    /**
     * Remove epfd_info.
     */
    int del_epfd(int fd, bool b_cleanup = false);
    void remove_epfd_from_list(epfd_info *epfd);

    /**
     * Remove cq_channel_info.
     */
    int del_cq_channel_fd(int fd, bool b_cleanup = false);

    /**
     * Remove tap_fd from tap_map.
     */
    void del_tapfd(int fd);

    void set_socket(int fd, sockinfo *si) { m_p_sockfd_map[fd] = si; }
    void clear_socket(int fd) { m_p_sockfd_map[fd] = nullptr; }

    /**
     * Call set_immediate_os_sample of the input fd.
     */
    inline bool set_immediate_os_sample(int fd);

    inline void reuse_sockfd(int fd, sockinfo *p_sfd_api_obj);
    inline void destroy_sockfd(sockinfo *p_sfd_api_obj);
    /**
     * Get sock_fd_api (sockinfo) by fd.
     */
    inline sockinfo *get_sockfd(int fd);

    /**
     * Get epfd_info by fd.
     */
    inline epfd_info *get_epfd(int fd);

    /**
     * Get cq_channel_info by fd.
     */
    inline cq_channel_info *get_cq_channel_fd(int fd);

    /**
     * Get rint_tap by tap fd.
     */
    inline ring_tap *get_tapfd(int fd);

    /**
     * Get the fd_map size.
     */
    inline int get_fd_map_size();

    /**
     * Remove fd from the collection of all epfd's
     */
    void remove_from_all_epfds(int fd, bool passthrough);

    /**
     * Remove everything from the collection.
     */
    void clear();
    void prepare_to_close();

    void offloading_rule_change_thread(bool offloaded, pthread_t tid);

    /**
     * Dump fd statistics using XLIO logger.
     */
    void statistics_print(int fd, vlog_levels_t log_level);

#if defined(DEFINED_NGINX)
    bool pop_socket_pool(int &fd, bool &add_to_udp_pool, int type);
    void push_socket_pool(sockinfo *sockfd);
    void handle_socket_pool(int fd);
#endif
private:
    template <typename cls> int del(int fd, bool b_cleanup, cls **map_type);
    template <typename cls> inline cls *get(int fd, cls **map_type);
    int del_socket(int fd, sockinfo **map_type);
    inline bool is_valid_fd(int fd);

    inline bool create_offloaded_sockets();

    // Fd collection timer implementation
    // This gives context to handle pending to remove fds.
    // In case of TCP we recheck if TCP socket is closable and delete
    // it if it does otherwise we run handle_timer of the socket to
    // progress the TCP connection.
    void handle_timer_expired(void *user_data);

    void statistics_print_helper(int fd, vlog_levels_t log_level);

private:
    int m_n_fd_map_size;
    sockinfo **m_p_sockfd_map;
    epfd_info **m_p_epfd_map;
    cq_channel_info **m_p_cq_channel_map;
    ring_tap **m_p_tap_map;

    epfd_info_list_t m_epfd_lst;
    // Contains fds which are in closing process
    sock_fd_api_list_t m_pending_to_remove_lst;

    const bool m_b_sysvar_offloaded_sockets;

    // if (m_b_sysvar_offloaded_sockets is true) contain all threads that need not be offloaded.
    // else contain all threads that need to be offloaded.
    offload_thread_rule_t m_offload_thread_rule;

#if defined(DEFINED_NGINX)
    bool m_use_socket_pool;
    std::stack<sockinfo *> m_socket_pool;
    int m_socket_pool_size;
    int m_socket_pool_counter;
#endif
};

inline bool fd_collection::is_valid_fd(int fd)
{
    if (fd < 0 || fd >= m_n_fd_map_size) {
        return false;
    }
    return true;
}

template <typename cls> inline cls *fd_collection::get(int fd, cls **map_type)
{
    if (!is_valid_fd(fd)) {
        return NULL;
    }

    cls *obj = map_type[fd];
    return obj;
}

inline bool fd_collection::set_immediate_os_sample(int fd)
{
    ring_tap *p_ring;

    lock();

    if ((p_ring = get_tapfd(fd))) {
        p_ring->set_tap_data_available();
        unlock();
        return true;
    }

    unlock();
    return false;
}

inline void fd_collection::reuse_sockfd(int fd, sockinfo *p_sfd_api_obj)
{
    lock();
    m_pending_to_remove_lst.erase(p_sfd_api_obj);
    m_p_sockfd_map[fd] = p_sfd_api_obj;
    --g_global_stat_static.n_pending_sockets;
    unlock();
}

inline void fd_collection::destroy_sockfd(sockinfo *p_sfd_api_obj)
{
    lock();
    --g_global_stat_static.n_pending_sockets;
    m_pending_to_remove_lst.erase(p_sfd_api_obj);
    p_sfd_api_obj->clean_socket_obj();
    unlock();
}

inline sockinfo *fd_collection::get_sockfd(int fd)
{
    return get(fd, m_p_sockfd_map);
}

inline epfd_info *fd_collection::get_epfd(int fd)
{
    return get(fd, m_p_epfd_map);
}

inline cq_channel_info *fd_collection::get_cq_channel_fd(int fd)
{
    return get(fd, m_p_cq_channel_map);
}

inline ring_tap *fd_collection::get_tapfd(int fd)
{
    return get(fd, m_p_tap_map);
}

inline int fd_collection::get_fd_map_size()
{
    return m_n_fd_map_size;
}

extern fd_collection *g_p_fd_collection;

inline sockinfo *fd_collection_get_sockfd(int fd)
{
    if (g_p_fd_collection) {
        return g_p_fd_collection->get_sockfd(fd);
    }
    return nullptr;
}

inline epfd_info *fd_collection_get_epfd(int fd)
{
    if (g_p_fd_collection) {
        return g_p_fd_collection->get_epfd(fd);
    }
    return nullptr;
}

#endif
