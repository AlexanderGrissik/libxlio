/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#ifndef _EPFD_INFO_H
#define _EPFD_INFO_H

#include <util/wakeup_pipe.h>
#include <sock/cleanable_obj.h>
#include <sock/sockinfo.h>

typedef xlio_list_t<sockinfo, sockinfo::ep_ready_fd_node_offset> ep_ready_fd_list_t;
typedef xlio_list_t<sockinfo, sockinfo::ep_info_fd_node_offset> fd_info_list_t;
typedef std::unordered_map<int, epoll_fd_rec> fd_info_map_t;
typedef std::unordered_map<ring *, int /*ref count*/> ring_map_t;
typedef std::deque<int> ready_cq_fd_q_t;

class epfd_info : public lock_mutex_recursive, public cleanable_obj, public wakeup_pipe {
public:
    epfd_info(int epfd, int size);
    ~epfd_info();

    /**
     * Lock and perform epoll_ctl.
     * Arguments the same as for epoll_ctl()
     */
    int ctl(int op, int fd, epoll_event *event);

    /**
     * Get the offloaded fds array and its length.
     * @param adress of the pointer to number of offloaded fds.
     * @param adress of the offloaded fds array.
     */
    void get_offloaded_fds_arr_and_size(int **p_p_num_offloaded_fds, int **p_p_offloadded_fds);

    /**
     * check if fd is cq fd according to the data.
     * if it is, save the fd in ready cq fds queue.
     * @param data field from event data
     * @return true if fd is cq fd
     */
    bool is_cq_fd(uint64_t data);

    /**
     * Get the original user data posted with this fd.
     * @param fd File descriptor.
     * @return Pointer to user data if the data for this fd was found.
     */
    epoll_fd_rec *get_fd_rec(int fd);

    /**
     * Called when fd is closed, to remove it from this set.
     * @param fd Closed file descriptor.
     */
    void fd_closed(int fd, bool passthrough = false);

    /**
     * @return Pointer to statistics block for this group
     */
    epoll_stats_t *stats();

    bool ring_poll_and_process_element(uint64_t *p_poll_sn_rx, uint64_t *p_poll_sn_tx,
                                       void *pv_fd_ready_array = nullptr);

    int ring_request_notification(uint64_t poll_sn_rx, uint64_t poll_sn_tx);

    void ring_wait_for_notification_and_process_element(uint64_t *p_poll_sn,
                                                        void *pv_fd_ready_array = nullptr);

    virtual void clean_obj();

    void statistics_print(vlog_levels_t log_level = VLOG_DEBUG);

    static inline size_t epfd_info_node_offset(void)
    {
        return NODE_OFFSET(epfd_info, epfd_info_node);
    }

    int get_epoll_fd() { return m_epfd; };
    int remove_fd_from_epoll_os(int fd);
    inline size_t get_fd_non_offloaded_size() { return m_fd_non_offloaded_map.size(); }
    inline size_t get_fd_offloaded_size() { return m_fd_offloaded_list.size(); }
    void insert_epoll_event_cb(sockinfo *sock_fd, uint32_t event_flags);
    void insert_epoll_event(sockinfo *sock_fd, uint32_t event_flags);
    void remove_epoll_event(sockinfo *sock_fd, uint32_t event_flags);
    void increase_ring_ref_count(ring *ring);
    void decrease_ring_ref_count(ring *ring);

private:
    int add_fd(int fd, epoll_event *event);
    int del_fd(int fd, bool passthrough = false);
    int mod_fd(int fd, epoll_event *event);

public:
    ep_ready_fd_list_t m_ready_fds;
    list_node<epfd_info, epfd_info::epfd_info_node_offset> epfd_info_node;

private:
    const int m_epfd;
    int m_size;
    int *m_p_offloaded_fds;
    int m_n_offloaded_fds;
    fd_info_map_t m_fd_non_offloaded_map;
    fd_info_list_t m_fd_offloaded_list;
    ring_map_t m_ring_map;
    lock_mutex_recursive m_ring_map_lock;
    ready_cq_fd_q_t m_ready_cq_fd_q;
    epoll_stats_t m_local_stats;
    epoll_stats_t *m_stats;
    int m_log_invalid_events;
};
#endif /* _EPFD_INFO_H */
