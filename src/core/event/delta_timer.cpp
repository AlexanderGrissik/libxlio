/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#include <stdlib.h>
#include <sys/time.h>
#include "utils/bullseye.h"
#include "utils/clock.h"
#include "vlogger/vlogger.h"
#include "core/util/sys_vars.h"
#include "core/util/utils.h"
#include "delta_timer.h"
#include "timer_handler.h"

#define MODULE_NAME "tmr:"

#define tmr_logpanic __log_panic
#define tmr_logerr   __log_err
#define tmr_logwarn  __log_warn
#define tmr_loginfo  __log_info
#define tmr_logdbg   __log_dbg
#define tmr_logfunc  __log_func
//#define tmr_logfuncall __log_funcall
#define tmr_logfuncall(fmt, ...)

#define IS_NODE_INVALID(_node_)                                                                    \
    (!_node_ || !_node_->handler || (_node_->req_type < 0 || _node_->req_type >= INVALID_TIMER))

timer::timer()
{
    m_list_head = nullptr;
    int ret = gettime(&m_ts_last);
    if (ret) {
        tmr_logerr("gettime() returned with value %d and error (errno %d %m)", ret, errno);
    }
}

timer::~timer()
{
    timer_node_t *iter = m_list_head;
    timer_node_t *to_free = nullptr;
    tmr_logfunc("");
    m_list_head = nullptr;
    // free all the list
    while (iter) {
        to_free = iter;
        iter = iter->next;
        free(to_free);
    }
}

void timer::add_new_timer(unsigned int timeout_msec, timer_node_t *node, timer_handler *handler,
                          void *user_data, timer_req_type_t req_type)
{
    node->handler = handler;
    node->req_type = req_type;
    node->user_data = user_data;
    node->orig_time_msec = timeout_msec;

    BULLSEYE_EXCLUDE_BLOCK_START
    if (IS_NODE_INVALID(node)) {
        free(node);
        return;
    }
    BULLSEYE_EXCLUDE_BLOCK_END

    insert_to_list(node);
    return;
}

void timer::wakeup_timer(timer_node_t *node)
{
    BULLSEYE_EXCLUDE_BLOCK_START
    if (IS_NODE_INVALID(node)) {
        return;
    }
    BULLSEYE_EXCLUDE_BLOCK_END

    remove_from_list(node);

    unsigned int orig_time = node->orig_time_msec;
    node->orig_time_msec = 0;
    insert_to_list(node);
    node->orig_time_msec = orig_time;

    return;
}

void timer::remove_timer(timer_node_t *node, timer_handler *handler)
{
    // Look for handler in the list if node wasen't indicated
    if (!node) {
        node = m_list_head;
        while (node) {
            if (node->handler == handler) { // node found
                break;
            }
            node = node->next;
        }
    }

    // Here we MUST have a valid node pointer
    BULLSEYE_EXCLUDE_BLOCK_START
    if (IS_NODE_INVALID(node) || (node->handler != handler)) {
        tmr_logfunc("bad <node,handler> combo for removale (%p,%p)", node, handler);
        return;
    }
    BULLSEYE_EXCLUDE_BLOCK_END

    // Invalidate node before freeing it
    node->handler = nullptr;
    node->req_type = INVALID_TIMER;

    // Remove & Free node
    remove_from_list(node);
    free(node);
    return;
}

void timer::remove_all_timers(timer_handler *handler)
{
    timer_node_t *node = m_list_head;
    timer_node_t *node_tmp = nullptr;

    // Look for handler in the list if node wasen't indicated
    while (node) {
        if (node->handler == handler) { // node found
            node_tmp = node;
            node = node->next;
            // Here we MUST have a valid node pointer
            BULLSEYE_EXCLUDE_BLOCK_START
            if (IS_NODE_INVALID(node_tmp) || (node_tmp->handler != handler)) {
                tmr_logfunc("bad <node,handler> combo for removale (%p,%p)", node_tmp, handler);
                continue;
            }
            BULLSEYE_EXCLUDE_BLOCK_END
            // Invalidate node before freeing it
            node_tmp->handler = nullptr;
            node_tmp->req_type = INVALID_TIMER;
            remove_from_list(node_tmp);
            // Remove & Free node
            free(node_tmp);
            // coverity[assigned_pointer:FALSE] /* Turn off coverity check,intended assign*/
            node_tmp = nullptr;
        } else {
            node = node->next;
        }
    }

    return;
}

int timer::update_timeout()
{
    int ret = 0, delta_msec = 0;
    timer_node_t *list_tmp = nullptr;
    struct timespec ts_now, ts_delta;

    ret = gettime(&ts_now);
    BULLSEYE_EXCLUDE_BLOCK_START
    if (ret) {
        tmr_logpanic("gettime() returned with error (errno %d %m)", ret);
        return INFINITE_TIMEOUT;
    }
    BULLSEYE_EXCLUDE_BLOCK_END
    // Find difference (subtract)
    ts_sub(&ts_now, &m_ts_last, &ts_delta);
    delta_msec = ts_to_msec(&ts_delta);

    // Save 'now' as 'last'
    if (delta_msec > 0) {
        m_ts_last = ts_now;
    }

    // empty list -> unlimited timeout
    if (!m_list_head) {
        tmr_logfunc("elapsed time: %d msec", delta_msec);
        ret = INFINITE_TIMEOUT;
        goto out;
    }

    // Check for timeout!
    list_tmp = m_list_head;
    while (delta_msec > 0 && list_tmp) {
        tmr_logfuncall("updating list node %p with elapsed time: %d msec", list_tmp, delta_msec);
        if ((int)list_tmp->delta_time_msec > delta_msec) {
            list_tmp->delta_time_msec -= delta_msec;
            break;
        } else {
            delta_msec -= list_tmp->delta_time_msec;
            list_tmp->delta_time_msec = 0;
        }
        list_tmp = list_tmp->next;
    }

    ret = m_list_head->delta_time_msec;

out:
    tmr_logfuncall("next timeout: %d msec", ret);
    return ret;
}

void timer::process_registered_timers()
{
    timer_node_t *iter = m_list_head;
    timer_node_t *next_iter;
    while (iter && (iter->delta_time_msec == 0)) {
        tmr_logfuncall("timer expired on %p", iter->handler);

        /* Special check is need to protect
         * from using destroyed object pointed by handler
         * See unregister_timer_event()
         * Object can be destoyed from another thread (lock protection)
         * and from current thread (lock and lock count condition)
         */
        if (iter->handler && !iter->lock_timer.trylock() &&
            (1 == iter->lock_timer.is_locked_by_me())) {
            iter->handler->handle_timer_expired(iter->user_data);
            iter->lock_timer.unlock();
        }
        next_iter = iter->next;

        switch (iter->req_type) {
        case PERIODIC_TIMER:
            // re-insert
            remove_from_list(iter);
            iter->prev = iter->next = nullptr;
            insert_to_list(iter);
            break;

        case ONE_SHOT_TIMER:
            remove_timer(iter, iter->handler);
            break;

            BULLSEYE_EXCLUDE_BLOCK_START
        case INVALID_TIMER:
            /* fallthrough */
        default:
            tmr_logwarn("invalid timer expired on %p", iter->handler);
            break;
        }
        BULLSEYE_EXCLUDE_BLOCK_END
        iter = next_iter;
    }
}

void timer::process_registered_timers_uncond()
{
    timer_node_t *iter = m_list_head;
    timer_node_t *next_iter;
    while (iter) {
        tmr_logfuncall("timer executed on %p", iter->handler);

        iter->handler->handle_timer_expired(iter->user_data);

        next_iter = iter->next;

        switch (iter->req_type) {
        case PERIODIC_TIMER:
            break;

        case ONE_SHOT_TIMER:
            remove_timer(iter, iter->handler);
            break;

            BULLSEYE_EXCLUDE_BLOCK_START
        case INVALID_TIMER:
            /* fallthrough */
        default:
            tmr_logwarn("invalid timer expired on %p", iter->handler);
            break;
        }
        BULLSEYE_EXCLUDE_BLOCK_END
        iter = next_iter;
    }
}

// insert allocated node to the list
void timer::insert_to_list(timer_node_t *new_node)
{
    unsigned int tmp_delta;
    timer_node_t *iter;
    timer_node_t *prev;

    if (!m_list_head) { // first node in the list
        new_node->delta_time_msec = new_node->orig_time_msec; // time from now
        new_node->next = nullptr;
        new_node->prev = nullptr;
        m_list_head = new_node;
        tmr_logfuncall("insert first node to list (handler %p, timer %d, delta time %d)",
                       new_node->handler, new_node->orig_time_msec, new_node->delta_time_msec);
        return;
    }
    // else: need to find the correct place in the list
    tmp_delta = new_node->orig_time_msec;
    iter = m_list_head;
    prev = nullptr;

    while (iter && tmp_delta >= iter->delta_time_msec) {
        tmp_delta = tmp_delta - iter->delta_time_msec;
        prev = iter;
        iter = iter->next;
    }

    new_node->delta_time_msec = tmp_delta;
    new_node->next = iter;
    new_node->prev = prev;
    if (prev) {
        prev->next = new_node;
    } else { // first node in the list
        m_list_head = new_node;
    }
    // update the delta time for the next element
    if (new_node->next) {
        new_node->next->delta_time_msec =
            new_node->next->delta_time_msec - new_node->delta_time_msec;
        new_node->next->prev = new_node;
    }
    tmr_logfuncall("insert new node to list  (handler %p, timer %d, delta time %d)",
                   new_node->handler, new_node->orig_time_msec, new_node->delta_time_msec);
}

// remove timer from list (without free)
// called after timer expired (as part of unregister timer, or while reregister periodic timer)
void timer::remove_from_list(timer_node_t *node)
{
    // remove from the list
    if (node->prev) { // not the first element in list
        node->prev->next = node->next;
    } else {
        m_list_head = node->next;
    }
    if (node->next) { // not the last element in list
        node->next->delta_time_msec = node->next->delta_time_msec + node->delta_time_msec;
        node->next->prev = node->prev;
    }
    tmr_logfuncall("removed node from list (handler %p, timer %d, delta time %d)", node->handler,
                   node->orig_time_msec, node->delta_time_msec);
}

const char *timer_req_type_str(timer_req_type_t type)
{
    switch (type) {
    case PERIODIC_TIMER:
        return "PERIODIC";
    case ONE_SHOT_TIMER:
        return "ONE SHOT";
        BULLSEYE_EXCLUDE_BLOCK_START
    case INVALID_TIMER:
        return "INVALID";
    default:
        return "Unknown timer type";
        BULLSEYE_EXCLUDE_BLOCK_END
    }
}

// code coverage
#if 0
void timer::debug_print_list()
{
	timer_node_t* iter = m_list_head;
	tmr_logdbg("");
	while (iter) {
		tmr_logdbg("node %p timer %d",iter, iter->delta_time_msec);
		iter = iter->next;
	}
}
#endif
