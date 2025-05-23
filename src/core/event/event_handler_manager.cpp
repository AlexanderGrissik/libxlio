/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#include "event_handler_manager.h"

#include <sys/epoll.h>
#include <rdma/rdma_cma.h>
#include <core/dev/net_device_table_mgr.h>
#include "core/dev/ring_allocation_logic.h"
#include "core/sock/fd_collection.h"
#include "core/sock/sock-redirect.h" // calling SYSCALL(epoll)()
#include "core/proto/route_table_mgr.h"
#include "timer_handler.h"
#include "event_handler_ibverbs.h"
#include "event_handler_rdma_cm.h"
#include "core/sock/sockinfo_tcp.h"
#include "core/util/instrumentation.h"

#define MODULE_NAME "evh:"

#define evh_logpanic   __log_panic
#define evh_logerr     __log_err
#define evh_logwarn    __log_warn
#define evh_loginfo    __log_info
#define evh_logdbg     __log_dbg
#define evh_logfunc    __log_func
#define evh_logfuncall __log_funcall

#undef VLOG_PRINTF_ENTRY
#define VLOG_PRINTF_ENTRY(log_level, log_fmt, log_args...)                                         \
    vlog_printf(log_level, MODULE_NAME "%d:%s(" log_fmt ")\n", __LINE__, __FUNCTION__, ##log_args)

#if (MAX_DEFINED_LOG_LEVEL < DEFINED_VLOG_DEBUG)
#define evh_logdbg_entry(log_fmt, log_args...) ((void)0)
#else
#define evh_logdbg_entry(log_fmt, log_args...)                                                     \
    do {                                                                                           \
        if (g_vlogger_level >= VLOG_DEBUG)                                                         \
            VLOG_PRINTF_ENTRY(VLOG_DEBUG, log_fmt, ##log_args);                                    \
    } while (0)
#endif

#if (MAX_DEFINED_LOG_LEVEL < DEFINED_VLOG_FINE)
#define evh_logfunc_entry(log_fmt, log_args...) ((void)0)
#else
#define evh_logfunc_entry(log_fmt, log_args...)                                                    \
    do {                                                                                           \
        if (g_vlogger_level >= VLOG_FUNC)                                                          \
            VLOG_PRINTF_ENTRY(VLOG_FUNC, log_fmt, ##log_args);                                     \
    } while (0)
#endif /* MAX_DEFINED_LOG_LEVEL */

#define INITIAL_EVENTS_NUM 64

event_handler_manager *g_p_event_handler_manager = nullptr;

pthread_t g_n_internal_thread_id = 0;

void *event_handler_manager::register_timer_event(int timeout_msec, timer_handler *handler,
                                                  timer_req_type_t req_type, void *user_data)
{
    evh_logdbg("timer handler '%p' registered %s timer for %d msec (user data: %p)", handler,
               timer_req_type_str(req_type), timeout_msec, user_data);
    BULLSEYE_EXCLUDE_BLOCK_START
    if (!handler || (req_type < 0 || req_type >= INVALID_TIMER)) {
        evh_logwarn("bad timer type (%d) or handler (%p)", req_type, handler);
        return nullptr;
    }
    BULLSEYE_EXCLUDE_BLOCK_END

    // malloc here the timer list node in order to return it to the app
    void *node = calloc(1, sizeof(struct timer_node_t));
    BULLSEYE_EXCLUDE_BLOCK_START
    if (!node) {
        evh_logdbg("malloc failure");
        throw_xlio_exception("malloc failure");
    }
    BULLSEYE_EXCLUDE_BLOCK_END

    timer_node_t *timer_node = (timer_node_t *)node;
    timer_node->lock_timer = lock_spin_recursive("timer");

    reg_action_t reg_action;
    memset(&reg_action, 0, sizeof(reg_action));
    reg_action.type = REGISTER_TIMER;
    reg_action.info.timer.handler = handler;
    reg_action.info.timer.user_data = user_data;
    reg_action.info.timer.node = node;
    reg_action.info.timer.timeout_msec = timeout_msec;
    reg_action.info.timer.req_type = req_type;
    post_new_reg_action(reg_action);
    return node;
}

void event_handler_manager::register_socket_timer_event(sockinfo_tcp *sock_tcp)
{
    evh_logdbg("Registering TCP socket timer: %p", sock_tcp);
    reg_action_t reg_action;
    memset(&reg_action, 0, sizeof(reg_action));
    reg_action.type = REGISTER_TCP_SOCKET_TIMER;
    reg_action.info.timer.user_data = sock_tcp;
    post_new_reg_action(reg_action);
}

void event_handler_manager::wakeup_timer_event(timer_handler *handler, void *node)
{
    evh_logdbg("timer handler '%p'", handler);
    BULLSEYE_EXCLUDE_BLOCK_START
    if (!handler) {
        evh_logwarn("bad handler (%p)", handler);
        return;
    }
    BULLSEYE_EXCLUDE_BLOCK_END
    reg_action_t reg_action;
    memset(&reg_action, 0, sizeof(reg_action));
    reg_action.type = WAKEUP_TIMER;
    reg_action.info.timer.handler = handler;
    reg_action.info.timer.node = node;
    post_new_reg_action(reg_action);
}

void event_handler_manager::unregister_timer_event(timer_handler *handler, void *node)
{
    evh_logdbg("timer handler '%p'", handler);
    reg_action_t reg_action;
    memset(&reg_action, 0, sizeof(reg_action));
    reg_action.type = UNREGISTER_TIMER;
    reg_action.info.timer.handler = handler;
    reg_action.info.timer.node = node;

    /* Special protection is needed to avoid scenario when deregistration is done
     * during timer_handler object destruction, timer node itself is not removed
     * and time for this timer node is expired. In this case there is no guarantee
     * to operate with timer_handler object.
     * See timer::process_registered_timers()
     * Do just lock() to protect timer_handler inside process_registered_timers()
     */
    if (node) {
        timer_node_t *timer_node = (timer_node_t *)node;
        timer_node->lock_timer.lock();
    }

    post_new_reg_action(reg_action);
}

void event_handler_manager::unregister_timers_event_and_delete(timer_handler *handler)
{
    evh_logdbg("timer handler '%p'", handler);
    reg_action_t reg_action;
    memset(&reg_action, 0, sizeof(reg_action));
    reg_action.type = UNREGISTER_TIMERS_AND_DELETE;
    reg_action.info.timer.handler = handler;
    post_new_reg_action(reg_action);
}

void event_handler_manager::unregister_socket_timer_and_delete(sockinfo_tcp *sock_tcp)
{
    evh_logdbg("Unregistering TCP socket timer: %p", sock_tcp);
    reg_action_t reg_action;
    memset(&reg_action, 0, sizeof(reg_action));
    reg_action.type = UNREGISTER_TCP_SOCKET_TIMER_AND_DELETE;
    reg_action.info.timer.user_data = sock_tcp;
    post_new_reg_action(reg_action);
}

void event_handler_manager::register_ibverbs_event(int fd, event_handler_ibverbs *handler,
                                                   void *channel, void *user_data)
{
    reg_action_t reg_action;
    memset(&reg_action, 0, sizeof(reg_action));
    reg_action.type = REGISTER_IBVERBS;
    reg_action.info.ibverbs.fd = fd;
    reg_action.info.ibverbs.handler = handler;
    reg_action.info.ibverbs.channel = channel;
    reg_action.info.ibverbs.user_data = user_data;
    post_new_reg_action(reg_action);
}

void event_handler_manager::unregister_ibverbs_event(int fd, event_handler_ibverbs *handler)
{
    reg_action_t reg_action;
    memset(&reg_action, 0, sizeof(reg_action));
    reg_action.type = UNREGISTER_IBVERBS;
    reg_action.info.ibverbs.fd = fd;
    reg_action.info.ibverbs.handler = handler;
    post_new_reg_action(reg_action);
}

void event_handler_manager::register_rdma_cm_event(int fd, void *id, void *cma_channel,
                                                   event_handler_rdma_cm *handler)
{
    reg_action_t reg_action;
    memset(&reg_action, 0, sizeof(reg_action));
    reg_action.type = REGISTER_RDMA_CM;
    reg_action.info.rdma_cm.fd = fd;
    reg_action.info.rdma_cm.id = id;
    reg_action.info.rdma_cm.handler = handler;
    reg_action.info.rdma_cm.cma_channel = cma_channel;
    post_new_reg_action(reg_action);
}

void event_handler_manager::unregister_rdma_cm_event(int fd, void *id)
{
    reg_action_t reg_action;
    memset(&reg_action, 0, sizeof(reg_action));
    reg_action.type = UNREGISTER_RDMA_CM;
    reg_action.info.rdma_cm.fd = fd;
    reg_action.info.rdma_cm.id = id;
    post_new_reg_action(reg_action);
}

void event_handler_manager::register_command_event(int fd, command *cmd)
{
    reg_action_t reg_action;

    evh_logdbg("Register command %s event", cmd->to_str().c_str());

    memset(&reg_action, 0, sizeof(reg_action));
    reg_action.type = REGISTER_COMMAND;
    reg_action.info.cmd.fd = fd;
    reg_action.info.cmd.cmd = cmd;
    post_new_reg_action(reg_action);
}

event_handler_manager::event_handler_manager(bool internal_thread_mode)
    : m_reg_action_q_lock("reg_action_q_lock")
    , m_b_sysvar_internal_thread_arm_cq_enabled(safe_mce_sys().internal_thread_arm_cq_enabled)
    , m_n_sysvar_timer_resolution_msec(safe_mce_sys().timer_resolution_msec)
{
    evh_logfunc("");

    m_cq_epfd = 0;
    m_epfd = -1;
    m_event_handler_tid = 0;

    if (!internal_thread_mode) {
        m_b_continue_running = true;
        return;
    }

    m_epfd = SYSCALL(epoll_create, INITIAL_EVENTS_NUM);
    BULLSEYE_EXCLUDE_BLOCK_START
    if (m_epfd == -1) {
        evh_logdbg("epoll_create failed on ibv device collection (errno=%d %m)", errno);
        free_evh_resources();
        throw_xlio_exception("epoll_create failed on ibv device collection");
    }
    BULLSEYE_EXCLUDE_BLOCK_END

    m_b_continue_running = true;

    wakeup_set_epoll_fd(m_epfd);
    going_to_sleep();
}

event_handler_manager::~event_handler_manager()
{
    free_evh_resources();
}

void event_handler_manager::free_evh_resources()
{
    evh_logfunc("");

    // Flag thread to stop on next loop
    stop_thread();
    evh_logfunc("Thread stopped");
}

// event handler main thread startup
void *event_handler_thread(void *_p_tgtObject)
{
    event_handler_manager *p_tgtObject = (event_handler_manager *)_p_tgtObject;
    g_n_internal_thread_id = pthread_self();
    evh_logdbg("Entering internal thread, id = %lu", g_n_internal_thread_id);

    if (strcmp(safe_mce_sys().internal_thread_cpuset, MCE_DEFAULT_INTERNAL_THREAD_CPUSET)) {
        std::string tasks_file(safe_mce_sys().internal_thread_cpuset);
        tasks_file += "/tasks";
        FILE *fp = fopen(tasks_file.c_str(), "w");
        BULLSEYE_EXCLUDE_BLOCK_START
        if (!fp) {
            evh_logpanic("Failed to open %s for writing", tasks_file.c_str());
        }
        if (fprintf(fp, "%d", gettid()) <= 0) {
            fclose(fp);
            evh_logpanic("Failed to add internal thread id to %s", tasks_file.c_str());
        }
        BULLSEYE_EXCLUDE_BLOCK_END
        fclose(fp);
        evh_logdbg("Internal thread added to cpuset %s.", safe_mce_sys().internal_thread_cpuset);

        // do set affinity now that we are on correct cpuset
        cpu_set_t cpu_set = safe_mce_sys().internal_thread_affinity;
        if (strcmp(safe_mce_sys().internal_thread_affinity_str, "-1")) {
            if (pthread_setaffinity_np(g_n_internal_thread_id, sizeof(cpu_set), &cpu_set)) {
                evh_logdbg("Internal thread affinity failed. Did you try to set affinity "
                           "outside of cpuset?");
            } else {
                evh_logdbg("Internal thread affinity is set.");
            }
        } else {
            evh_logdbg("Internal thread affinity not set.");
        }
    }

    void *ret = p_tgtObject->thread_loop();
    evh_logdbg("Ending internal thread");
    return ret;
}

int event_handler_manager::start_thread()
{
    cpu_set_t cpu_set;
    pthread_attr_t tattr;

    if (!m_b_continue_running) {
        return -1;
    }

    if (m_event_handler_tid != 0) {
        return 0;
    }

    // m_reg_action_q.reserve(); //todo change to vector and reserve

    BULLSEYE_EXCLUDE_BLOCK_START
    if (pthread_attr_init(&tattr)) {
        evh_logpanic("Failed to initialize thread attributes");
    }
    BULLSEYE_EXCLUDE_BLOCK_END

    cpu_set = safe_mce_sys().internal_thread_affinity;
    if (strcmp(safe_mce_sys().internal_thread_affinity_str, "-1") &&
        !strcmp(safe_mce_sys().internal_thread_cpuset,
                MCE_DEFAULT_INTERNAL_THREAD_CPUSET)) { // no affinity
        BULLSEYE_EXCLUDE_BLOCK_START
        if (pthread_attr_setaffinity_np(&tattr, sizeof(cpu_set), &cpu_set)) {
            evh_logpanic("Failed to set CPU affinity");
        }
        BULLSEYE_EXCLUDE_BLOCK_END
    } else {
        evh_logdbg("Internal thread affinity not set.");
    }

    int ret = pthread_create(&m_event_handler_tid, &tattr, event_handler_thread, this);
    if (ret) {
        // maybe it's the cset issue? try without affinity
        evh_logwarn("Failed to start event handler thread with thread affinity - trying without. "
                    "[errno=%d %s]",
                    ret, strerror(ret));
        BULLSEYE_EXCLUDE_BLOCK_START
        if (pthread_attr_init(&tattr)) {
            evh_logpanic("Failed to initialize thread attributes");
        }
        if (pthread_create(&m_event_handler_tid, &tattr, event_handler_thread, this)) {
            evh_logpanic("Failed to start event handler thread");
        }
        BULLSEYE_EXCLUDE_BLOCK_END
    }

    pthread_attr_destroy(&tattr);

    evh_logdbg("Started event handler thread");
    return 0;
}

void event_handler_manager::stop_thread()
{
    if (!m_b_continue_running) {
        return;
    }
    m_b_continue_running = false;

    if (!g_is_forked_child) {

        do_wakeup();

        // Wait for thread exit
        if (m_event_handler_tid) {
            pthread_join(m_event_handler_tid, nullptr);
            evh_logdbg("event handler thread stopped");
        } else {
            evh_logdbg("event handler thread not running");
        }
    }
    m_event_handler_tid = 0;

    // Close main epfd and signaling socket
    if (m_epfd >= 0) {
        SYSCALL(close, m_epfd);
    }
    m_epfd = -1;
}

void event_handler_manager::update_epfd(int fd, int operation, int events)
{
    epoll_event ev = {0, {nullptr}};

    if (m_epfd < 0) {
        return;
    }

    ev.events = events;
    ev.data.fd = fd;
    BULLSEYE_EXCLUDE_BLOCK_START
    if ((SYSCALL(epoll_ctl, m_epfd, operation, fd, &ev) < 0) &&
        (!(errno == ENOENT || errno == EBADF))) {
        const char *operation_str[] = {"", "ADD", "DEL", "MOD"};
        evh_logerr("epoll_ctl(%d, %s, fd=%d) failed (errno=%d %m)", m_epfd,
                   operation_str[operation], fd, errno);
    }
    BULLSEYE_EXCLUDE_BLOCK_END
}

const char *event_handler_manager::reg_action_str(event_action_type_e reg_action_type)
{
    switch (reg_action_type) {
    case REGISTER_TCP_SOCKET_TIMER:
        return "REGISTER_TCP_SOCKET_TIMER";
    case UNREGISTER_TCP_SOCKET_TIMER_AND_DELETE:
        return "UNREGISTER_TCP_SOCKET_TIMER_AND_DELETE";
    case REGISTER_TIMER:
        return "REGISTER_TIMER";
    case UNREGISTER_TIMER:
        return "UNREGISTER_TIMER";
    case UNREGISTER_TIMERS_AND_DELETE:
        return "UNREGISTER_TIMERS_AND_DELETE";
    case REGISTER_IBVERBS:
        return "REGISTER_IBVERBS";
    case UNREGISTER_IBVERBS:
        return "UNREGISTER_IBVERBS";
    case REGISTER_RDMA_CM:
        return "REGISTER_RDMA_CM";
    case UNREGISTER_RDMA_CM:
        return "UNREGISTER_RDMA_CM";
    case REGISTER_COMMAND:
        return "REGISTER_COMMAND";
    case UNREGISTER_COMMAND:
        return "UNREGISTER_COMMAND";
        BULLSEYE_EXCLUDE_BLOCK_START
    default:
        return "UNKNOWN";
        BULLSEYE_EXCLUDE_BLOCK_END
    }
}

// get new action of event (register / unregister), and post to the thread's pipe
void event_handler_manager::post_new_reg_action(reg_action_t &reg_action)
{
    if (!m_b_continue_running) {
        return;
    }

    start_thread();

    evh_logfunc("add event action %s (%d)", reg_action_str(reg_action.type), reg_action.type);

    bool is_empty = false;
    m_reg_action_q_lock.lock();
    if (m_p_reg_action_q_to_push_to->empty()) {
        is_empty = true;
    }
    m_p_reg_action_q_to_push_to->push_back(reg_action);
    m_reg_action_q_lock.unlock();
    if (is_empty) {
        do_wakeup();
    }
}

void event_handler_manager::priv_register_timer_handler(timer_reg_info_t &info)
{
    m_timer.add_new_timer(info.timeout_msec, (timer_node_t *)info.node, info.handler,
                          info.user_data, info.req_type);
}

void event_handler_manager::priv_wakeup_timer_handler(timer_reg_info_t &info)
{
    m_timer.wakeup_timer((timer_node_t *)info.node);
}

void event_handler_manager::priv_unregister_timer_handler(timer_reg_info_t &info)
{
    m_timer.remove_timer((timer_node_t *)info.node, info.handler);
}

void event_handler_manager::priv_unregister_all_handler_timers(timer_reg_info_t &info)
{
    m_timer.remove_all_timers(info.handler);
}

void event_handler_manager::priv_prepare_ibverbs_async_event_queue(event_handler_map_t::iterator &i)
{
    evh_logdbg_entry("");

    int cnt = 0;
    struct pollfd poll_fd = {/*.fd=*/0, /*.events=*/POLLIN, /*.revents=*/0};

    if (i == m_event_handler_map.end()) {
        evh_logdbg("No event handler");
        return;
    }

    poll_fd.fd = i->second.ibverbs_ev.fd;

    // change the blocking mode of the async event queue
    set_fd_block_mode(poll_fd.fd, false);

    // empty the async event queue
    while (SYSCALL(poll, &poll_fd, 1, 0) > 0) {
        process_ibverbs_event(i);
        cnt++;
    }
    evh_logdbg("Emptied %d Events", cnt);
    NOT_IN_USE(cnt); // Suppress --enable-opt-log=high warning
}

void event_handler_manager::priv_register_ibverbs_events(ibverbs_reg_info_t &info)
{
    event_handler_map_t::iterator i;
    i = m_event_handler_map.find(info.fd);
    if (i == m_event_handler_map.end()) {
        m_event_handler_map[info.fd] = event_data_t(EV_IBVERBS, info);
        i = m_event_handler_map.find(info.fd);

        priv_prepare_ibverbs_async_event_queue(i);

        update_epfd(info.fd, EPOLL_CTL_ADD, EPOLLIN | EPOLLPRI);
        evh_logdbg("%d added to event_handler_map_t!", info.fd);
    }
    BULLSEYE_EXCLUDE_BLOCK_START
    if (i->second.type != EV_IBVERBS) {
        evh_logerr("fd=%d: is already handling events of different type", info.fd);
        return;
    }

    ibverbs_event_map_t::iterator j;
    j = i->second.ibverbs_ev.ev_map.find(info.handler);
    if (j != i->second.ibverbs_ev.ev_map.end()) {
        evh_logerr("Event for %d/%p already registered", info.fd, info.handler);
        return;
    }
    BULLSEYE_EXCLUDE_BLOCK_END

    ibverbs_event_t vv;
    vv.handler = info.handler;
    vv.user_data = info.user_data;
    i->second.ibverbs_ev.ev_map[info.handler] = vv;

    return;
}

void event_handler_manager::priv_unregister_ibverbs_events(ibverbs_reg_info_t &info)
{

    event_handler_map_t::iterator i;
    ibverbs_event_map_t::iterator j;
    int n = 0;

    i = m_event_handler_map.find(info.fd);

    BULLSEYE_EXCLUDE_BLOCK_START
    if (i == m_event_handler_map.end()) {
        evh_logerr("Event for %d/%p already does not exist", info.fd, info.handler);
        return;
    }

    if (i->second.type != EV_IBVERBS) {
        evh_logerr("fd=%d: is already handling events of different type", info.fd);
        return;
    }

    n = i->second.ibverbs_ev.ev_map.size();

    if (n < 1) {
        evh_logerr("Event for %d/%p already does not exist", info.fd, info.handler);
        return;
    }

    j = i->second.ibverbs_ev.ev_map.find(info.handler);
    if (j == i->second.ibverbs_ev.ev_map.end()) {
        evh_logerr("event for %d/%p does not exist", info.fd, info.handler);
        return;
    }
    BULLSEYE_EXCLUDE_BLOCK_END

    i->second.ibverbs_ev.ev_map.erase(j);
    if (n == 1) {
        update_epfd(info.fd, EPOLL_CTL_DEL, EPOLLIN | EPOLLPRI);
        m_event_handler_map.erase(i);
        evh_logdbg("%d erased from event_handler_map_t!", info.fd);
    }
}

void event_handler_manager::priv_register_rdma_cm_events(rdma_cm_reg_info_t &info)
{
    evh_logfunc_entry("fd=%d, event_handler_id=%p", info.fd, info.id);

    // Handle the new registration
    event_handler_map_t::iterator iter_fd = m_event_handler_map.find(info.fd);
    if (iter_fd == m_event_handler_map.end()) {
        evh_logdbg("Adding new channel (fd %d, id %p, handler %p)", info.fd, info.id, info.handler);
        m_event_handler_map[info.fd] = event_data_t(EV_RDMA_CM, info);

        update_epfd(info.fd, EPOLL_CTL_ADD, EPOLLIN | EPOLLPRI);
    } else {
        BULLSEYE_EXCLUDE_BLOCK_START
        if (iter_fd->second.type != EV_RDMA_CM) {
            evh_logerr("fd=%d: is already handling events of different type", info.fd);
            return;
        }
        event_handler_rdma_cm_map_t::iterator iter_id =
            iter_fd->second.rdma_cm_ev.map_rdma_cm_id.find(info.id);
        if (iter_id == iter_fd->second.rdma_cm_ev.map_rdma_cm_id.end()) {
            evh_logdbg("Adding to exitsing channel fd %d (id %p, handler %p)", info.fd, info.id,
                       info.handler);
            iter_fd->second.rdma_cm_ev.map_rdma_cm_id[info.id] = info.handler;
            iter_fd->second.rdma_cm_ev.n_ref_count++;
            if (iter_fd->second.rdma_cm_ev.cma_channel != info.cma_channel) {
                evh_logerr(
                    "Trying to change the channel processing cb's on a registered fd %d (by id %p)",
                    info.fd, info.id);
            }
        } else {
            evh_logerr("Channel-id pair <%d, %p> already registered (handler %p)", info.fd, info.id,
                       info.handler);
        }
        BULLSEYE_EXCLUDE_BLOCK_END
    }
}

void event_handler_manager::priv_unregister_rdma_cm_events(rdma_cm_reg_info_t &info)
{
    evh_logfunc_entry("fd=%d, id=%p", info.fd, info.id);

    event_handler_map_t::iterator iter_fd = m_event_handler_map.find(info.fd);
    if (iter_fd != m_event_handler_map.end()) {
        BULLSEYE_EXCLUDE_BLOCK_START
        if (iter_fd->second.type != EV_RDMA_CM) {
            evh_logerr("fd=%d: is already handling events of different type", info.fd);
            return;
        }
        BULLSEYE_EXCLUDE_BLOCK_END
        event_handler_rdma_cm_map_t::iterator iter_id =
            iter_fd->second.rdma_cm_ev.map_rdma_cm_id.find(info.id);
        BULLSEYE_EXCLUDE_BLOCK_START
        if (iter_id != iter_fd->second.rdma_cm_ev.map_rdma_cm_id.end()) {
            BULLSEYE_EXCLUDE_BLOCK_END
            evh_logdbg("Removing from channel %d, id %p", info.fd, info.id);
            iter_fd->second.rdma_cm_ev.map_rdma_cm_id.erase(iter_id);
            iter_fd->second.rdma_cm_ev.n_ref_count--;
            if (iter_fd->second.rdma_cm_ev.n_ref_count == 0) {
                update_epfd(info.fd, EPOLL_CTL_DEL, EPOLLIN | EPOLLPRI);
                m_event_handler_map.erase(iter_fd);
                evh_logdbg("Removed channel <%d %p>", info.fd, info.id);
            }
        } else {
            evh_logerr("Channel-id pair <%d %p> not found", info.fd, info.id);
        }
    } else {
        evh_logdbg("Channel %d not found", info.fd);
    }
}

void event_handler_manager::priv_register_command_events(command_reg_info_t &info)
{
    // In case this is new registration need to add netlink fd to the epfd
    event_handler_map_t::iterator iter_fd = m_event_handler_map.find(info.fd);
    if (iter_fd == m_event_handler_map.end()) {
        evh_logdbg("Adding new channel (fd %d)", info.fd);
        m_event_handler_map[info.fd] = event_data_t(EV_COMMAND, info);
        update_epfd(info.fd, EPOLL_CTL_ADD, EPOLLIN | EPOLLPRI);
    }
}

void event_handler_manager::priv_unregister_command_events(command_reg_info_t &info)
{

    event_handler_map_t::iterator iter_fd = m_event_handler_map.find(info.fd);
    if (iter_fd == m_event_handler_map.end()) {
        evh_logdbg(" channel wasn't found (fd %d)", info.fd);

    } else if (iter_fd->first != EV_COMMAND) {
        evh_logdbg(" This fd (%d) no longer COMMAND type fd", info.fd);
    } else {
        update_epfd(info.fd, EPOLL_CTL_DEL, EPOLLIN | EPOLLPRI);
    }
}

void event_handler_manager::handle_registration_action(reg_action_t &reg_action)
{
    if (!m_b_continue_running && reg_action.type != UNREGISTER_TIMERS_AND_DELETE) {
        return;
    }

    evh_logfunc("event action %d", reg_action.type);
    sockinfo_tcp *sock;
    switch (reg_action.type) {
    case REGISTER_TCP_SOCKET_TIMER:
        sock = reinterpret_cast<sockinfo_tcp *>(reg_action.info.timer.user_data);
        sock->get_tcp_timer_collection()->add_new_timer(sock);
        break;
    case UNREGISTER_TCP_SOCKET_TIMER_AND_DELETE:
        sock = reinterpret_cast<sockinfo_tcp *>(reg_action.info.timer.user_data);
        sock->get_tcp_timer_collection()->remove_timer(sock);
        delete sock;
        break;
    case REGISTER_TIMER:
        priv_register_timer_handler(reg_action.info.timer);
        break;
    case WAKEUP_TIMER:
        priv_wakeup_timer_handler(reg_action.info.timer);
        break;
    case UNREGISTER_TIMER:
        priv_unregister_timer_handler(reg_action.info.timer);
        break;
    case REGISTER_IBVERBS:
        priv_register_ibverbs_events(reg_action.info.ibverbs);
        break;
    case UNREGISTER_IBVERBS:
        priv_unregister_ibverbs_events(reg_action.info.ibverbs);
        break;
    case REGISTER_RDMA_CM:
        priv_register_rdma_cm_events(reg_action.info.rdma_cm);
        break;
    case UNREGISTER_RDMA_CM:
        priv_unregister_rdma_cm_events(reg_action.info.rdma_cm);
        break;
    case REGISTER_COMMAND:
        priv_register_command_events(reg_action.info.cmd);
        break;
    case UNREGISTER_COMMAND:
        priv_unregister_command_events(reg_action.info.cmd);
        break;
    case UNREGISTER_TIMERS_AND_DELETE:
        priv_unregister_all_handler_timers(reg_action.info.timer);
        delete reg_action.info.timer.handler;
        reg_action.info.timer.handler = nullptr;
        break;
        BULLSEYE_EXCLUDE_BLOCK_START
    default:
        evh_logerr("illegal event action! (%d)", reg_action.type);
        break;
        BULLSEYE_EXCLUDE_BLOCK_END
    }
    return;
}

void event_handler_manager::query_for_ibverbs_event(int async_fd)
{
    evh_logfunc_entry("");

    struct pollfd poll_fd;
    event_handler_map_t::iterator i;

    poll_fd.events = POLLIN | POLLPRI;
    poll_fd.revents = 0;
    poll_fd.fd = async_fd;

    // ibverbs events should be read only from the internal thread context
    if (pthread_self() != m_event_handler_tid) {
        return;
    }

    // Check for ready events
    if (SYSCALL(poll, &poll_fd, 1, 0) <= 0) {
        return;
    }

    // Verify handler exists in map
    if ((i = m_event_handler_map.find(async_fd)) == m_event_handler_map.end()) {
        return;
    }

    process_ibverbs_event(i);
}

void event_handler_manager::statistics_print(dump_type_t dump_type, int fd, vlog_levels_t log_level)
{
    if (m_b_continue_running) {
        switch (dump_type) {
        case DUMP_FD:
            if (g_p_fd_collection) {
                g_p_fd_collection->statistics_print(fd, log_level);
            }
            break;
        case DUMP_ROUTE:
            if (g_p_route_table_mgr) {
                g_p_route_table_mgr->dump_tbl();
            }
            break;
        case DUMP_NEIGH:
            // Not implemented yet
            break;
        default:
            evh_logdbg("Impossible statistics dump request (type=%d).", dump_type);
        }
    }
}

void event_handler_manager::process_ibverbs_event(event_handler_map_t::iterator &i)
{
    evh_logfunc_entry("");

    //
    // Pre handling
    //
    struct ibv_context *hca = (struct ibv_context *)i->second.ibverbs_ev.channel;
    struct ibv_async_event ibv_event;

    IF_VERBS_FAILURE(ibv_get_async_event(hca, &ibv_event))
    {
        vlog_levels_t _level =
            (errno == EBADF) ? VLOG_DEBUG : VLOG_ERROR; // EBADF may returned during plugout
        vlog_printf(_level, "[%d] Received HCA event but failed to get it (errno=%d %m)\n",
                    hca->async_fd, errno);
        return;
    }
    ENDIF_VERBS_FAILURE;
    evh_logdbg("[%d] Received ibverbs event %s (%d)", hca->async_fd,
               priv_ibv_event_desc_str(ibv_event.event_type), ibv_event.event_type);

    //
    // Notify Event to handlers
    //
    for (ibverbs_event_map_t::iterator pos = i->second.ibverbs_ev.ev_map.begin();
         pos != i->second.ibverbs_ev.ev_map.end(); pos++) {
        pos->second.handler->handle_event_ibverbs_cb(&ibv_event, pos->second.user_data);
    }

    evh_logdbg("[%d] Completed ibverbs event %s (%d)", hca->async_fd,
               priv_ibv_event_desc_str(ibv_event.event_type), ibv_event.event_type);

    //
    // Post handling
    //
    ibv_ack_async_event(&ibv_event);
}

void event_handler_manager::process_rdma_cm_event(event_handler_map_t::iterator &iter_fd)
{
    // Read the notification event channel
    struct rdma_event_channel *cma_channel =
        (struct rdma_event_channel *)iter_fd->second.rdma_cm_ev.cma_channel;
    struct rdma_cm_event *p_tmp_cm_event = nullptr;
    struct rdma_cm_event cma_event;

    evh_logfunc_entry("cma_channel %p (fd = %d)", cma_channel, cma_channel->fd);

    BULLSEYE_EXCLUDE_BLOCK_START
    // Get rdma_cm event
    if (rdma_get_cm_event(cma_channel, &p_tmp_cm_event)) {
        evh_logerr("rdma_get_cm_event failed on cma_channel %p (fd = %d) (errno=%d %s)",
                   cma_channel, cma_channel->fd, errno, strerror(errno));
        return;
    }
    if (!p_tmp_cm_event) {
        evh_logpanic("rdma_get_cm_event succeeded but the returned event is NULL on cma_channel %p "
                     "(fd = %d) (errno=%d %s)",
                     cma_channel, cma_channel->fd, errno, strerror(errno));
    }
    BULLSEYE_EXCLUDE_BLOCK_END

    // Duplicate rdma_cm event to local memory
    memcpy(&cma_event, p_tmp_cm_event, sizeof(cma_event));

    // Ack  rdma_cm event (free)
    rdma_ack_cm_event(p_tmp_cm_event);
    evh_logdbg("[%d] Received rdma_cm event %s (%d)", cma_channel->fd,
               priv_rdma_cm_event_type_str(cma_event.event), cma_event.event);

    void *cma_id = (void *)cma_event.id;
    if (cma_event.listen_id) { // we assume that cma_listen_id != NULL in case of connect request
        cma_id = (void *)cma_event.listen_id;
    }

    // Find registered event handler
    if (cma_id) {
        event_handler_rdma_cm_map_t::iterator iter_id =
            iter_fd->second.rdma_cm_ev.map_rdma_cm_id.find(cma_id);
        if (iter_id != iter_fd->second.rdma_cm_ev.map_rdma_cm_id.end()) {
            event_handler_rdma_cm *handler = iter_id->second;

            // Call the registered event handler with event to be handled
            if (handler) {
                handler->handle_event_rdma_cm_cb(&cma_event);
            }
        } else {
            evh_logdbg("Can't find event_handler for ready event_handler_id %p (fd=%d)", cma_id,
                       iter_fd->first);
        }
    }

    evh_logdbg("[%d] Completed rdma_cm event %s (%d)", cma_channel->fd,
               priv_rdma_cm_event_type_str(cma_event.event), cma_event.event);
}

/*
The main loop actions:
    1) update timeout + handle registers that theire timeout expiered
    2) epoll_wait
    3) handle new registrations/unregistrations
    4) update timeout + handle registers that theire timeout expiered
    5) handle new events
*/

void *event_handler_manager::thread_loop()
{
    int timeout_msec;
    int maxevents = INITIAL_EVENTS_NUM;
    struct pollfd poll_fd;
    struct epoll_event *p_events =
        (struct epoll_event *)malloc(sizeof(struct epoll_event) * maxevents);
    BULLSEYE_EXCLUDE_BLOCK_START
    if (!p_events) {
        evh_logdbg("malloc failure");
        throw_xlio_exception("malloc failure");
    }
    BULLSEYE_EXCLUDE_BLOCK_END

    poll_fd.events = POLLIN | POLLPRI;
    poll_fd.revents = 0;
    while (m_b_continue_running) {
        // update timer and get timeout
        timeout_msec = m_timer.update_timeout();
        if (timeout_msec == 0) {
            // at least one timer has expired!
            m_timer.process_registered_timers();
            continue;
        }

        if (m_b_sysvar_internal_thread_arm_cq_enabled && m_cq_epfd == 0 &&
            g_p_net_device_table_mgr) {
            m_cq_epfd = g_p_net_device_table_mgr->global_ring_epfd_get();
            if (m_cq_epfd > 0) {
                epoll_event evt = {0, {nullptr}};
                evt.events = EPOLLIN | EPOLLPRI;
                evt.data.fd = m_cq_epfd;
                SYSCALL(epoll_ctl, m_epfd, EPOLL_CTL_ADD, m_cq_epfd, &evt);
            }
        }

        uint64_t poll_sn_rx = 0;
        uint64_t poll_sn_tx = 0;
        if (m_b_sysvar_internal_thread_arm_cq_enabled && m_cq_epfd > 0 &&
            g_p_net_device_table_mgr) {
            g_p_net_device_table_mgr->global_ring_poll_and_process_element(&poll_sn_rx, &poll_sn_tx,
                                                                           nullptr);
            int ret =
                g_p_net_device_table_mgr->global_ring_request_notification(poll_sn_rx, poll_sn_tx);
            if (ret > 0) {
                g_p_net_device_table_mgr->global_ring_poll_and_process_element(
                    &poll_sn_rx, &poll_sn_tx, nullptr);
            }
        }

        // Make sure we sleep for a minimum of X milli seconds
        if (timeout_msec > 0) {
            if ((int)m_n_sysvar_timer_resolution_msec > timeout_msec) {
                timeout_msec = m_n_sysvar_timer_resolution_msec;
            }
        }

        evh_logfuncall("calling SYSCALL(epoll) with %d msec timeout", timeout_msec);
        int ret = SYSCALL(epoll_wait, m_epfd, p_events, maxevents, timeout_msec);
        if (ret < 0) {
            evh_logfunc("epoll returned with error, errno=%d %m)", errno);
            continue;
        }
        evh_logfuncall("SYSCALL(epoll) found %d ready fds", ret);

        // check pipe
        for (int idx = 0; (idx < ret) && (m_b_continue_running); ++idx) {
            if (m_b_sysvar_internal_thread_arm_cq_enabled && p_events[idx].data.fd == m_cq_epfd &&
                g_p_net_device_table_mgr) {
                g_p_net_device_table_mgr->global_ring_wait_for_notification_and_process_element(
                    &poll_sn_rx, nullptr);
            } else if (is_wakeup_fd(p_events[idx].data.fd)) {
                // a request for registration was sent
                m_reg_action_q_lock.lock();
                reg_action_q_t *temp = m_p_reg_action_q_to_push_to;
                m_p_reg_action_q_to_push_to = m_p_reg_action_q_to_pop_from;
                m_p_reg_action_q_to_pop_from = temp;
                return_from_sleep();
                remove_wakeup_fd();
                going_to_sleep();
                m_reg_action_q_lock.unlock();

                reg_action_t reg_action;
                while (!m_p_reg_action_q_to_pop_from->empty()) {
                    reg_action = m_p_reg_action_q_to_pop_from->front();
                    m_p_reg_action_q_to_pop_from->pop_front();
                    handle_registration_action(reg_action);
                }
            }
        }

        if ((m_timer.update_timeout() == 0) && (m_b_continue_running)) {
            // at least one timer has expired!
            m_timer.process_registered_timers();
        }

        // process ready event channels
        for (int idx = 0; (idx < ret) && (m_b_continue_running); ++idx) {
            // if (p_events[idx].events & (EPOLLERR|EPOLLHUP))
            //	evh_logdbg("error in fd %d",p_events[idx].data.fd );

            int fd = p_events[idx].data.fd;

            if (m_b_sysvar_internal_thread_arm_cq_enabled && fd == m_cq_epfd) {
                continue;
            }

            evh_logfunc("Processing fd %d", fd);

            if (is_wakeup_fd(fd)) { // the pipe was already handled
                continue;
            }

            event_handler_map_t::iterator i = m_event_handler_map.find(fd);
            if (i == m_event_handler_map.end()) {
                // No event handler - this is probably a poll_os event!
                if (!g_p_fd_collection->set_immediate_os_sample(fd)) {
                    evh_logdbg("No event handler (fd=%d)", fd);
                }
                continue;
            }

            switch (i->second.type) {
            case EV_RDMA_CM:
                int result;
                poll_fd.fd = fd;
                result = SYSCALL(poll, &poll_fd, 1, 0);
                if (result == 0) {
                    evh_logdbg("error in fd %d", fd);
                    break;
                }
                process_rdma_cm_event(i);
                break;
            case EV_IBVERBS:
                process_ibverbs_event(i);
                break;
            case EV_COMMAND:
                i->second.command_ev.cmd->execute();
                break;
                BULLSEYE_EXCLUDE_BLOCK_START
            default:
                evh_logerr("Unknow event on fd=%d", fd);
                BULLSEYE_EXCLUDE_BLOCK_END
            }
        } // for idx

        if (ret == maxevents) {
            struct epoll_event *p_events_new;
            // increase the events array
            maxevents *= 2;
            p_events_new = (struct epoll_event *)realloc((void *)p_events,
                                                         sizeof(struct epoll_event) * maxevents);
            BULLSEYE_EXCLUDE_BLOCK_START
            if (!p_events_new) {
                evh_logpanic("realloc failure");
            }
            p_events = p_events_new;
            BULLSEYE_EXCLUDE_BLOCK_END
        }

    } // while (m_b_continue_running)

    free(p_events);

    return nullptr;
}
