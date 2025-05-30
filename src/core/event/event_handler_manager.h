/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#ifndef EVENT_HANDLER_MANAGER_H
#define EVENT_HANDLER_MANAGER_H

#include <map>
#include <deque>
#include "vlogger/vlogger.h"
#include "utils/lock_wrapper.h"
#include "core/util/wakeup_pipe.h"
#include "core/netlink/netlink_wrapper.h"
#include "core/infra/subject_observer.h"
#include "core/event/command.h"
#include "core/event/delta_timer.h"
#include "core/util/xlio_stats.h"

class timer_handler;
class event_handler_ibverbs;
class event_handler_rdma_cm;
class sockinfo_tcp;

typedef std::map<void * /*event_handler_id*/, event_handler_rdma_cm * /*p_event_handler*/>
    event_handler_rdma_cm_map_t;

typedef enum {
    REGISTER_TCP_SOCKET_TIMER,
    UNREGISTER_TCP_SOCKET_TIMER_AND_DELETE,
    REGISTER_TIMER,
    WAKEUP_TIMER, /* NOT AVAILABLE FOR GROUPED TIMERS */
    UNREGISTER_TIMER,
    UNREGISTER_TIMERS_AND_DELETE,
    REGISTER_IBVERBS,
    UNREGISTER_IBVERBS,
    REGISTER_RDMA_CM,
    UNREGISTER_RDMA_CM,
    REGISTER_COMMAND,
    UNREGISTER_COMMAND
} event_action_type_e;

struct ibverbs_event_t {
    event_handler_ibverbs *handler;
    void *user_data;
};

struct rdma_cm_ev_t {
    int n_ref_count; // number of event_handler on this fd
    event_handler_rdma_cm_map_t map_rdma_cm_id; // each event_handler class maps with it's own
                                                // event_handler_id (referenced as void*)
    void *cma_channel; // meaning here for the rdma_event_channel object
};

typedef std::map<event_handler_ibverbs *, ibverbs_event_t> ibverbs_event_map_t;

struct ibverbs_ev_t {
    int fd;
    void *channel;
    ibverbs_event_map_t ev_map;
};

struct command_ev_t {
    command *cmd;
};

struct timer_reg_info_t {
    timer_handler *handler;
    void *node;
    unsigned int timeout_msec;
    void *user_data;
    timer_req_type_t req_type;
};

struct ibverbs_reg_info_t {
    event_handler_ibverbs *handler;
    int fd;
    void *channel;
    void *user_data;
};

struct rdma_cm_reg_info_t {
    event_handler_rdma_cm *handler;
    int fd;
    void *id;
    void *cma_channel;
};

struct command_reg_info_t {
    int fd;
    command *cmd;
};

struct reg_action_t {
    event_action_type_e type;
    union {
        timer_reg_info_t timer;
        ibverbs_reg_info_t ibverbs;
        rdma_cm_reg_info_t rdma_cm;
        command_reg_info_t cmd;
    } info;
};

typedef std::deque<struct reg_action_t> reg_action_q_t;

enum ev_type {
    EV_IBVERBS,
    EV_RDMA_CM,
    EV_COMMAND,
};

struct event_data_t {
    ev_type type;
    ibverbs_ev_t ibverbs_ev;
    rdma_cm_ev_t rdma_cm_ev;
    command_ev_t command_ev;
    event_data_t() = default;
    event_data_t(ev_type t, const ibverbs_reg_info_t &info)
        : type(t)
        , ibverbs_ev {}
        , rdma_cm_ev {}
        , command_ev {}
    {
        ibverbs_ev.fd = info.fd;
        ibverbs_ev.channel = info.channel;
    }
    event_data_t(ev_type t, const rdma_cm_reg_info_t &info)
        : type(t)
        , ibverbs_ev {}
        , rdma_cm_ev {}
        , command_ev {}
    {
        rdma_cm_ev.n_ref_count = 1;
        rdma_cm_ev.map_rdma_cm_id[info.id] = info.handler;
        rdma_cm_ev.cma_channel = info.cma_channel;
    }
    event_data_t(ev_type t, const command_reg_info_t &info)
        : type(t)
        , ibverbs_ev {}
        , rdma_cm_ev {}
        , command_ev {}
    {
        command_ev.cmd = info.cmd;
    }
};

typedef std::map<int /*fd*/, event_data_t> event_handler_map_t;
typedef std::map<timer_handler *, void *> timer_list_t;

/*
** Class event_handler_manager
** The event manager object listens on the registered channels and distributes the incoming events
** to the appropriate registered event_handlers objects by their registered id's.
** All registered objects must implememtn the event_handler class which is the registered callback
*function.
*/
class event_handler_manager : public wakeup_pipe {
public:
    event_handler_manager(bool internal_thread_mode = true);
    ~event_handler_manager();

    void *register_timer_event(int timeout_msec, timer_handler *handler, timer_req_type_t req_type,
                               void *user_data);
    void wakeup_timer_event(timer_handler *handler, void *node);
    void unregister_timer_event(timer_handler *handler, void *node);
    void unregister_timers_event_and_delete(timer_handler *handler);

    void register_socket_timer_event(sockinfo_tcp *sock_tcp);
    void unregister_socket_timer_and_delete(sockinfo_tcp *sock_tcp);

    void register_ibverbs_event(int fd, event_handler_ibverbs *handler, void *channel,
                                void *user_data);
    void unregister_ibverbs_event(int fd, event_handler_ibverbs *handler);

    void register_rdma_cm_event(int fd, void *id, void *cma_channel,
                                event_handler_rdma_cm *handler);
    void unregister_rdma_cm_event(int fd, void *id);

    void register_command_event(int fd, command *cmd);

    void *thread_loop();
    void stop_thread();
    bool is_running() { return m_b_continue_running; };

    void update_epfd(int fd, int operation, int events);
    void query_for_ibverbs_event(int async_fd);
    void statistics_print(dump_type_t dump_type, int fd, vlog_levels_t log_level);

protected:
    pthread_t m_event_handler_tid;
    bool m_b_continue_running = false;
    int m_cq_epfd;
    int m_epfd;

    // pipe for the event registration handling
    reg_action_q_t m_reg_action_q1;
    reg_action_q_t m_reg_action_q2;
    reg_action_q_t *m_p_reg_action_q_to_push_to = &m_reg_action_q1;
    reg_action_q_t *m_p_reg_action_q_to_pop_from = &m_reg_action_q2;
    lock_spin m_reg_action_q_lock;
    timer m_timer;

    const bool m_b_sysvar_internal_thread_arm_cq_enabled;
    const uint32_t m_n_sysvar_timer_resolution_msec;

    event_handler_map_t m_event_handler_map;

    void priv_register_timer_handler(timer_reg_info_t &info);
    void priv_wakeup_timer_handler(timer_reg_info_t &info);
    void priv_unregister_timer_handler(timer_reg_info_t &info);
    void priv_unregister_all_handler_timers(timer_reg_info_t &info);
    void priv_register_ibverbs_events(ibverbs_reg_info_t &info);
    void priv_unregister_ibverbs_events(ibverbs_reg_info_t &info);
    void priv_register_rdma_cm_events(rdma_cm_reg_info_t &info);
    void priv_unregister_rdma_cm_events(rdma_cm_reg_info_t &info);
    void priv_register_command_events(command_reg_info_t &info);
    void priv_unregister_command_events(command_reg_info_t &info);
    void priv_prepare_ibverbs_async_event_queue(event_handler_map_t::iterator &i);

    const char *reg_action_str(event_action_type_e reg_action_type);
    virtual void post_new_reg_action(reg_action_t &reg_action);
    void handle_registration_action(reg_action_t &reg_action);
    void process_ibverbs_event(event_handler_map_t::iterator &i);
    void process_rdma_cm_event(event_handler_map_t::iterator &i);
    int start_thread();

    void event_channel_post_process_for_rdma_events(void *p_event);
    void *event_channel_pre_process_for_rdma_events(void *p_event_channel_handle, void **p_event);

    void free_evh_resources(void);
};

extern event_handler_manager *g_p_event_handler_manager;

extern pthread_t g_n_internal_thread_id;

#endif
