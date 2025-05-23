/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#include "poll_call.h"

#include <vlogger/vlogger.h>
#include <util/vtypes.h>
#include <sock/sockinfo.h>
#include <sock/sock-redirect.h>
#include <sock/fd_collection.h>
#include <dev/net_device_table_mgr.h>

#define MODULE_NAME "poll_call:"

iomux_func_stats_t g_poll_stats;

poll_call::poll_call(int *off_rfds_buffer, offloaded_mode_t *off_modes_buffer, int *lookup_buffer,
                     pollfd *working_fds_arr, pollfd *fds, nfds_t nfds, int timeout,
                     const sigset_t *__sigmask /* = NULL */)
    : io_mux_call(off_rfds_buffer, off_modes_buffer, 0, __sigmask)
    , m_nfds(nfds)
    , m_timeout(timeout)
    , m_lookup_buffer(lookup_buffer)
    , m_orig_fds(fds)
{
    nfds_t i;
    int fd;
    m_fds = nullptr;

    // create stats
    m_p_stats = &g_poll_stats;
    xlio_stats_instance_get_poll_block(m_p_stats);

    // Collect offloaded fds and remove all tcp (skip_os) sockets from m_fds
    for (i = 0; i < m_nfds; ++i) {
        // Very important to initialize this to 0 it is not done be default
        m_orig_fds[i].revents = 0;

        // We need to initialize m_fds[i].revents in case we already copied it from m_orig_fds
        if (m_fds) {
            m_fds[i].revents = 0;
        }

        fd = m_orig_fds[i].fd;
        sockinfo *temp_sock_fd_api = fd_collection_get_sockfd(fd);
        if (temp_sock_fd_api && (temp_sock_fd_api->get_type() == FD_TYPE_SOCKET)) {
            // POLLERR and POLLHUP are always enabled implicitly and considered as READ by XLIO
            offloaded_mode_t off_mode = OFF_READ;
            if (m_orig_fds[i].events & POLLOUT) {
                off_mode = (offloaded_mode_t)(off_mode | OFF_WRITE);
            }

            __log_func("---> fd=%d IS SET for read or write!", fd);
            m_lookup_buffer[m_num_all_offloaded_fds] = i;
            m_p_all_offloaded_fds[m_num_all_offloaded_fds] = fd;
            m_p_offloaded_modes[m_num_all_offloaded_fds] = off_mode;
            ++m_num_all_offloaded_fds;

            // We will do copy only in case we have at least one offloaded socket
            if (!m_fds) {
                m_fds = working_fds_arr;
                // m_fds will be working array and m_orig_fds is the pointer to user fds - we
                // cannot modify it
                memcpy(m_fds, m_orig_fds, m_nfds * sizeof(fds[0]));
            }

            if (temp_sock_fd_api->skip_os_select()) {
                __log_func("fd=%d must be skipped from os r poll()", fd);
                m_fds[i].fd = -1;
            } else if (m_orig_fds[i].events & POLLIN) {
                if (temp_sock_fd_api->is_readable(nullptr)) {
                    io_mux_call::update_fd_array(&m_fd_ready_array, fd);
                    m_n_ready_rfds++;
                    m_n_all_ready_fds++;
                } else {
                    // Instructing the socket to sample the OS immediately to prevent hitting
                    // EAGAIN on recvfrom(), after iomux returned a shadow fd as ready (only for
                    // non-blocking sockets)
                    temp_sock_fd_api->set_immediate_os_sample();
                }
            }
        }
    }

    // TODO: No need to have two arrays m_fds and m_orig_fds in case there is no offloaded sockets
    if (!m_num_all_offloaded_fds) {
        m_fds = m_orig_fds;
    }
    __log_func("num all offloaded_fds=%d", m_num_all_offloaded_fds);
}

void poll_call::prepare_to_block()
{
    m_cqepfd = g_p_net_device_table_mgr->global_ring_epfd_get();

    // add cq
    m_fds[m_nfds].events = POLLIN;
    m_fds[m_nfds].revents = 0;
    m_fds[m_nfds].fd = m_cqepfd;
}

bool poll_call::wait_os(bool zero_timeout)
{
    __log_func("calling os poll: %d", m_nfds);
    if (m_sigmask) {
        struct timespec to, *pto = nullptr;
        if (zero_timeout) {
            to.tv_sec = to.tv_nsec = 0;
            pto = &to;
        } else if (m_timeout >= 0) {
            to.tv_sec = m_timeout / 1000;
            to.tv_nsec = (m_timeout % 1000) * 1000000;
            pto = &to;
        }
        m_n_all_ready_fds = SYSCALL(ppoll, m_fds, m_nfds, pto, m_sigmask);
    } else {
        m_n_all_ready_fds = SYSCALL(poll, m_fds, m_nfds, zero_timeout ? 0 : m_timeout);
    }
    if (m_n_all_ready_fds < 0) {
        xlio_throw_object(io_mux_call::io_error);
    }

    if (m_n_all_ready_fds > 0) {
        __log_dbg("wait_os() returned with %d", m_n_all_ready_fds);
        copy_to_orig_fds();
    }
    return false; // No cq_fd in poll() event
}

bool poll_call::wait(const timeval &elapsed)
{
    // poll fds and cq
    int timeout;
    struct timespec to, *pto = nullptr;

    if (m_timeout < 0) {
        timeout = m_timeout;
    } else {
        timeout = m_timeout - tv_to_msec(&elapsed);
        if (timeout < 0) {
            // Already reached timeout
            return false;
        }
    }
    if (m_sigmask) {
        to.tv_sec = m_timeout / 1000;
        to.tv_nsec = (m_timeout % 1000) * 1000000;
        pto = &to;
        m_n_all_ready_fds = SYSCALL(ppoll, m_fds, m_nfds + 1, pto, m_sigmask);
    } else {
        m_n_all_ready_fds = SYSCALL(poll, m_fds, m_nfds + 1, timeout);
    }

    if (m_n_all_ready_fds > 0 && m_fds[m_nfds].revents) {
        // CQ was returned - remove it from the count
        --m_n_all_ready_fds;
        if (m_n_all_ready_fds > 0) {
            copy_to_orig_fds();
        }
        return true;
    }

    if (m_n_all_ready_fds < 0) {
        xlio_throw_object(io_mux_call::io_error);
    }

    copy_to_orig_fds();
    return false;
}

bool poll_call::is_timeout(const timeval &elapsed)
{
    return m_timeout >= 0 && m_timeout <= tv_to_msec(&elapsed);
}

void poll_call::set_offloaded_rfd_ready(int fd_index)
{
    if (m_p_offloaded_modes[fd_index] & OFF_READ) {

        int evt_index = m_lookup_buffer[fd_index];
        if (!m_orig_fds[evt_index].revents) {
            ++m_n_all_ready_fds;
        }
        if ((m_orig_fds[evt_index].events & POLLIN) && !(m_orig_fds[evt_index].revents & POLLIN)) {
            m_orig_fds[evt_index].revents |= POLLIN;
            ++m_n_ready_rfds;
        }
    }
}

void poll_call::set_offloaded_wfd_ready(int fd_index)
{
    if (m_p_offloaded_modes[fd_index] & OFF_WRITE) {
        int evt_index = m_lookup_buffer[fd_index];
        if (!m_orig_fds[evt_index].revents) {
            ++m_n_all_ready_fds;
        }
        if ((m_orig_fds[evt_index].events & POLLOUT) &&
            !(m_orig_fds[evt_index].revents & POLLOUT) &&
            !(m_orig_fds[evt_index].revents & POLLHUP)) {
            /* POLLOUT and POLLHUP are mutually exclusive */
            m_orig_fds[evt_index].revents |= POLLOUT;
            ++m_n_ready_wfds;
        }
    }
}

void poll_call::set_offloaded_efd_ready(int fd_index, int errors)
{
    if (m_p_offloaded_modes[fd_index] & OFF_RDWR) {
        int evt_index = m_lookup_buffer[fd_index];
        if (!m_orig_fds[evt_index].revents) {
            ++m_n_all_ready_fds;
        }
        bool got_errors = false;
        if ((errors & POLLHUP) && !(m_orig_fds[evt_index].revents & POLLHUP)) {
            m_orig_fds[evt_index].revents |= POLLHUP;
            if (m_orig_fds[evt_index].revents & POLLOUT) {
                /* POLLOUT and POLLHUP are mutually exclusive */
                m_orig_fds[evt_index].revents &= ~POLLOUT;
            }
            got_errors = true;
        }
        if ((errors & POLLERR) && !(m_orig_fds[evt_index].revents & POLLERR)) {
            m_orig_fds[evt_index].revents |= POLLERR;
            got_errors = true;
        }
        if (got_errors) {
            ++m_n_ready_efds;
        }
    }
}

void poll_call::set_rfd_ready(int fd)
{
    int fd_index;

    // TODO make this more efficient
    for (fd_index = 0; fd_index < *m_p_num_all_offloaded_fds; ++fd_index) {
        if (m_p_all_offloaded_fds[fd_index] == fd) {
            set_offloaded_rfd_ready(fd_index);
        }
    }
}
void poll_call::set_wfd_ready(int fd)
{
    int fd_index;

    // TODO make this more efficient
    for (fd_index = 0; fd_index < *m_p_num_all_offloaded_fds; ++fd_index) {
        if (m_p_all_offloaded_fds[fd_index] == fd) {
            set_offloaded_wfd_ready(fd_index);
        }
    }
}

void poll_call::set_efd_ready(int fd, int errors)
{
    int fd_index;

    // TODO make this more efficient
    for (fd_index = 0; fd_index < *m_p_num_all_offloaded_fds; ++fd_index) {
        if (m_p_all_offloaded_fds[fd_index] == fd) {
            set_offloaded_efd_ready(fd_index, errors);
        }
    }
}

void poll_call::copy_to_orig_fds()
{
    // No need to copy anything in case there are no offloaded sockets.
    if (!m_num_all_offloaded_fds) {
        return;
    }
    int ready_fds = m_n_all_ready_fds;
    for (nfds_t i = 0; i < m_nfds; i++) {
        if (m_fds[i].revents) {
            m_orig_fds[i].revents = m_fds[i].revents;
            ready_fds--;
            if (!ready_fds) {
                return;
            }
        }
    }
}
