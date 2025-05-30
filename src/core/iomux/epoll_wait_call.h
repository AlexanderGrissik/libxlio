/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#ifndef _EPOLL_WAIT_CALL_H
#define _EPOLL_WAIT_CALL_H

#include <sys/epoll.h>
#include <iomux/epfd_info.h>

#include "io_mux_call.h"

class epfd_info;

/**
 * @class poll_call
 * Functor for poll()
 */
class epoll_wait_call : public io_mux_call {
public:
    /**
     * Create an epoll_wait call.
     * @param extra_events_buffer Array of at least maxevents size.
     * @param ready_event_map_buffer Array of at least maxevents size.
     *
     * Rest of the arguments are the same as for poll() library function.
     * @throws io_mux_call::io_error
     */
    epoll_wait_call(epoll_event *extra_events_buffer, offloaded_mode_t *off_modes_buffer, int epfd,
                    epoll_event *events, int maxevents, int timeout,
                    const sigset_t *sigmask = nullptr);
    virtual ~epoll_wait_call();

    /// @override
    virtual void set_offloaded_rfd_ready(int fd_index);
    virtual void set_offloaded_wfd_ready(int fd_index);

    /// @override
    virtual void prepare_to_block();

    /// @override
    virtual bool wait_os(bool zero_timeout);

    /// @override
    virtual bool wait(const timeval &elapsed);

    /// @override
    virtual bool is_timeout(const timeval &elapsed);

    /// @override
    virtual void set_rfd_ready(int fd);

    /// @override
    virtual void set_wfd_ready(int fd);

    /// @override
    virtual void set_efd_ready(int fd, int errors);

    /// @override
    virtual void lock();

    /// @override
    virtual void unlock();

    /// @override
    virtual bool check_all_offloaded_sockets();

    void init_offloaded_fds();

    int get_current_events();

    bool handle_epoll_event(bool is_ready, uint32_t events, sockinfo *socket_object, int index);

protected:
    virtual bool ring_poll_and_process_element();

    virtual int ring_request_notification();

    virtual void ring_wait_for_notification_and_process_element(void *pv_fd_ready_array);

private:
    bool _wait(int timeout);

    /// Parameters for the call
    const int m_epfd;
    epoll_event *const m_events;
    const int m_maxevents;
    const int m_timeout;

    epoll_event *m_p_ready_events;
    epfd_info *m_epfd_info;
};

#endif
