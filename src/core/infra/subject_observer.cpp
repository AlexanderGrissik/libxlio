/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#include <mutex>
#include "vlogger/vlogger.h"
#include "core/infra/subject_observer.h"

#define MODULE_NAME "subject_observer"

#define sub_obs_logerr     __log_info_err
#define sub_obs_logwarn    __log_info_warn
#define sub_obs_loginfo    __log_info_info
#define sub_obs_logdbg     __log_info_dbg
#define sub_obs_logfunc    __log_info_func
#define sub_obs_logfuncall __log_info_funcall

bool subject::register_observer(IN const observer *const new_observer)
{
    if (new_observer == NULL) {
        //		sub_obs_logdbg("[%s] observer (NULL)", to_str());
        return false;
    }

    std::lock_guard<decltype(m_lock)> lock(m_lock);
    if (m_observers.count((observer *)new_observer) > 0) {
        //		sub_obs_logdbg("[%s] Observer is already registered (%p)", to_str(), new_observer);
        return false;
    }
    m_observers.insert((observer *)new_observer);
    //	sub_obs_logdbg("[%s] Successfully registered new_observer %s", to_str(),
    // new_observer->to_str());
    return true;
}

bool subject::unregister_observer(IN const observer *const old_observer)
{
    if (old_observer == NULL) {
        //		sub_obs_logdbg("[%s] observer (NULL)", to_str());
        return false;
    }

    std::lock_guard<decltype(m_lock)> lock(m_lock);
    m_observers.erase((observer *)old_observer);
    //	sub_obs_logdbg("[%s] Successfully unregistered old_observer %s",to_str(),
    // old_observer->to_str());
    return true;
}

void subject::notify_observers(event *ev /*=NULL*/)
{
    //	sub_obs_logdbg("[%s]", to_str());

    std::lock_guard<decltype(m_lock)> lock(m_lock);
    for (observers_t::iterator iter = m_observers.begin(); iter != m_observers.end(); iter++) {
        if (ev) {
            (*iter)->notify_cb(ev);
        } else {
            (*iter)->notify_cb();
        }
    }
}
