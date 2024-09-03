/*
 * Copyright (c) 2001-2024 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 *
 * This software is available to you under a choice of one of two
 * licenses.  You may choose to be licensed under the terms of the GNU
 * General Public License (GPL) Version 2, available from the file
 * COPYING in the main directory of this source tree, or the
 * BSD license below:
 *
 *     Redistribution and use in source and binary forms, with or
 *     without modification, are permitted provided that the following
 *     conditions are met:
 *
 *      - Redistributions of source code must retain the above
 *        copyright notice, this list of conditions and the following
 *        disclaimer.
 *
 *      - Redistributions in binary form must reproduce the above
 *        copyright notice, this list of conditions and the following
 *        disclaimer in the documentation and/or other materials
 *        provided with the distribution.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

#include <algorithm>
#include <thread>
#include <cinttypes>
#include <sys/mman.h>
#include <doca_buf.h>
#include <sock/sock-app.h>
#include "dev/hw_queue_rx.h"
#include "dev/buffer_pool.h"
#include "dev/ring_simple.h"
#include "dev/rfs_rule.h"
#include "dev/cq_mgr_rx_regrq.h"
#include "dev/cq_mgr_rx_strq.h"

#undef MODULE_NAME
#define MODULE_NAME "hw_queue_rx"

#define hwqrx_logpanic   __log_info_panic
#define hwqrx_logerr     __log_info_err
#define hwqrx_logwarn    __log_info_warn
#define hwqrx_loginfo    __log_info_info
#define hwqrx_logdbg     __log_info_dbg
#define hwqrx_logfunc    __log_info_func
#define hwqrx_logfuncall __log_info_funcall

#define ALIGN_WR_DOWN(_num_wr_) (std::max(32, ((_num_wr_) & ~(0xf))))

hw_queue_rx::hw_queue_rx(ring_simple *ring, ib_ctx_handler *ib_ctx,
                         ibv_comp_channel *rx_comp_event_channel, uint16_t vlan)
    : m_doca_mmap(g_buffer_pool_rx_rwqe->get_doca_mmap())
    , m_p_ring(ring)
    , m_p_ib_ctx_handler(ib_ctx)
    , m_n_sysvar_rx_num_wr_to_post_recv(safe_mce_sys().rx_num_wr_to_post_recv)
    , m_rx_num_wr(align32pow2(safe_mce_sys().rx_num_wr))
    , m_n_sysvar_rx_prefetch_bytes_before_poll(safe_mce_sys().rx_prefetch_bytes_before_poll)
    , m_vlan(vlan)
{
    hwqrx_logfunc("");

    if (!prepare_doca_rxq()) {
        throw_xlio_exception("Failed to create DOCA RXQ");
    }

    if (!configure_rq(rx_comp_event_channel)) {
        throw_xlio_exception("Failed to create RQ");
    }
}

hw_queue_rx::~hw_queue_rx()
{
    hwqrx_logfunc("");

    m_rq.reset(nullptr); // Must be destroyed before RX CQ.
    m_doca_rxq.reset(nullptr); // Must be destroyed before RX PE.

    if (m_rq_wqe_idx_to_wrid) {
        if (0 != munmap(m_rq_wqe_idx_to_wrid, m_rx_num_wr * sizeof(*m_rq_wqe_idx_to_wrid))) {
            hwqrx_logerr(
                "Failed deallocating memory with munmap m_rq_wqe_idx_to_wrid (errno=%d %m)", errno);
        }
        m_rq_wqe_idx_to_wrid = nullptr;
    }

    if (m_p_cq_mgr_rx) {
        delete m_p_cq_mgr_rx;
        m_p_cq_mgr_rx = nullptr;
    }

    delete[] m_ibv_rx_sg_array;
    delete[] m_ibv_rx_wr_array;

    g_buffer_pool_rx_rwqe->put_buffers_thread_safe(&m_rx_pool, m_rx_pool.size());

    hwqrx_logdbg("Rx buffer poll: %ld free global buffers available",
                 g_buffer_pool_rx_rwqe->get_free_count());
}

bool hw_queue_rx::prepare_doca_rxq()
{
    doca_dev *dev = m_p_ib_ctx_handler->get_doca_device();
    doca_devinfo *devinfo = doca_dev_as_devinfo(dev);

    doca_error_t type_supported = doca_eth_rxq_cap_is_type_supported(
        devinfo, DOCA_ETH_RXQ_TYPE_REGULAR, DOCA_ETH_RXQ_DATA_PATH_TYPE_CPU);

    uint32_t max_burst_size = 0U;
    uint32_t max_packet_size = 0U;
    doca_error_t err1 = doca_eth_rxq_cap_get_max_burst_size(devinfo, &max_burst_size);
    doca_error_t err2 = doca_eth_rxq_cap_get_max_packet_size(devinfo, &max_packet_size);

    if (DOCA_IS_ERROR(type_supported) || DOCA_IS_ERROR(err1) || DOCA_IS_ERROR(err2)) {
        PRINT_DOCA_ERR(hwqrx_logerr, type_supported, "doca_eth_rxq_cap_is_type_supported");
        PRINT_DOCA_ERR(hwqrx_logerr, err1, "doca_eth_rxq_cap_get_max_burst_size");
        PRINT_DOCA_ERR(hwqrx_logerr, err2, "doca_eth_rxq_cap_get_max_packet_size");
        return false;
    }

    hwqrx_loginfo("RXQ caps MaxBurstSize %u, MaxPacketSize %u, Dev:%s", max_burst_size,
                  max_packet_size, m_p_ib_ctx_handler->get_ibname().c_str());

    m_rxq_burst_size = (align32pow2(safe_mce_sys().rx_num_wr));
    if (m_rxq_burst_size > max_burst_size) {
        hwqrx_logwarn("Decreasing BurstSize %u to capability %u.", m_rxq_burst_size,
                      max_burst_size);
        m_rxq_burst_size = max_burst_size;
    }

    hwqrx_loginfo("Creating DOCA RXQ MaxBurstSize: %u, MaxPacketSize: %u, Dev:%s", m_rxq_burst_size,
                  max_packet_size, m_p_ib_ctx_handler->get_ibname().c_str());

    doca_eth_rxq *rxq = nullptr;
    // For DOCA_ETH_RXQ_TYPE_REGULAR the max_packet_size has no effect but cannot be 0.
    doca_error_t err = doca_eth_rxq_create(dev, m_rxq_burst_size, max_packet_size, &rxq);
    if (DOCA_IS_ERROR(err)) {
        PRINT_DOCA_ERR(hwqrx_logerr, err, "doca_eth_rxq_create");
        return false;
    }

    m_doca_rxq.reset(rxq);
    m_doca_ctx_rxq = doca_eth_rxq_as_doca_ctx(rxq);
    m_rxq_task_debt = m_rxq_burst_size;
    m_rx_buff_pool_treshold_max = m_rxq_burst_size * 2U;
    m_rx_buff_pool_treshold_min = m_rxq_burst_size;
    m_rx_debt_submit_treshold = m_rxq_burst_size / 2U;

    err = doca_ctx_set_user_data(m_doca_ctx_rxq, {.ptr = this});
    if (DOCA_IS_ERROR(err)) {
        PRINT_DOCA_ERR(hwqrx_logerr, err, "doca_ctx_set_user_data ctx/hw_queue_rx: %p,%p",
                       m_doca_ctx_rxq, this);
        return false;
    }

    err = doca_eth_rxq_set_type(m_doca_rxq.get(), DOCA_ETH_RXQ_TYPE_REGULAR);
    if (DOCA_IS_ERROR(err)) {
        PRINT_DOCA_ERR(hwqrx_logerr, err, "doca_eth_rxq_get_type_supported");
        return false;
    }

    err = doca_eth_rxq_task_recv_set_conf(m_doca_rxq.get(), rx_task_completion_cb, rx_task_error_cb,
                                          m_rxq_burst_size);
    if (DOCA_IS_ERROR(err)) {
        PRINT_DOCA_ERR(hwqrx_logerr, err, "doca_eth_rxq_task_recv_set_conf rxq: %p max-tasks: %u",
                       m_doca_rxq.get(), m_rxq_burst_size);
        return false;
    }

    doca_pe *pe;
    err = doca_pe_create(&pe);
    if (DOCA_IS_ERROR(err)) {
        PRINT_DOCA_ERR(hwqrx_logerr, err, "doca_pe_create");
        return false;
    }

    m_doca_pe.reset(pe);

    err = doca_pe_connect_ctx(pe, m_doca_ctx_rxq);
    if (DOCA_IS_ERROR(err)) {
        PRINT_DOCA_ERR(hwqrx_logerr, err, "doca_pe_connect_ctx pe/ctx/rxq: %p,%p,%p", pe,
                       m_doca_ctx_rxq, m_doca_rxq.get());
        return false;
    }

#if defined(DEFINED_NGINX) || defined(DEFINED_ENVOY)
    // For some scenario with forking usage we may want to distribute CQs across multiple
    // CPUs to improve CPS in case of multiple processes.

    // TODO: [DOCA] Replace with real information from DOCA.
    int comp_channel_num = 1U;

    // TODO: [DOCA] Currently not functional.
    if (safe_mce_sys().app.distribute_cq_interrupts && g_p_app->get_worker_id() >= 0 &&
        m_p_ib_ctx_handler->is_notification_affinity_supported()) {
        uint32_t comp_ch = g_p_app->get_worker_id() % comp_channel_num;
        hwqrx_logdbg("Setting PE completion affinity: %" PRIu32 ", pid: %d", comp_ch, getpid());

        err = doca_pe_set_notification_affinity(pe, comp_ch);
        if (DOCA_IS_ERROR(err)) {
            PRINT_DOCA_ERR(hwqrx_logerr, err,
                           "doca_pe_set_notification_affinity pe/ctx/rxq: %p,%p,%p", pe,
                           m_doca_ctx_rxq, m_doca_rxq.get());
        }
    }
#endif

    err = doca_pe_get_notification_handle(pe, &m_notification_handle);
    if (DOCA_IS_ERROR(err)) {
        PRINT_DOCA_ERR(hwqrx_logerr, err, "doca_pe_get_notification_handle");
        return false;
    }

    doca_buf_inventory *inventory = nullptr;
    err = doca_buf_inventory_create(m_rxq_burst_size, &inventory);
    if (DOCA_IS_ERROR(err)) {
        PRINT_DOCA_ERR(hwqrx_logerr, err, "doca_buf_inventory_create");
        return false;
    }

    m_doca_inventory.reset(inventory);

    err = doca_buf_inventory_start(inventory);
    if (DOCA_IS_ERROR(err)) {
        PRINT_DOCA_ERR(hwqrx_logerr, err, "doca_buf_inventory_start");
        return false;
    }

    hwqrx_logdbg("Created DOCA RXQ and PE %p/%p", m_doca_rxq.get(), m_doca_pe.get());
    return true;
}

void hw_queue_rx::submit_rxq_tasks()
{
    fill_buffers_from_global_pool();

    size_t batch_size = std::min(static_cast<size_t>(m_rxq_task_debt), m_rx_pool.size());
    if (batch_size > 0) {
        while (--batch_size > 0) {
            if (unlikely(!submit_rxq_task(DOCA_TASK_SUBMIT_FLAG_NONE))) {
                break;
            }
        }

        submit_rxq_task(DOCA_TASK_SUBMIT_FLAG_FLUSH);
    }
}

bool hw_queue_rx::submit_rxq_task(uint32_t task_flag)
{
    doca_eth_rxq_task_recv *rx_doca_task = nullptr;
    doca_buf *rx_doca_buf = nullptr;
    mem_buf_desc_t *buff = m_rx_pool.front();
    doca_error_t rc = doca_buf_inventory_buf_get_by_addr(
        m_doca_inventory.get(), m_doca_mmap, buff->p_buffer, buff->sz_buffer, &rx_doca_buf);
    if (DOCA_IS_ERROR(rc)) {
        PRINT_DOCA_ERR(hwqrx_logerr, rc, "doca_buf_inventory_buf_get_by_data");
        return false;
    }

    rc = doca_eth_rxq_task_recv_allocate_init(m_doca_rxq.get(), rx_doca_buf, {.ptr = buff},
                                              &rx_doca_task);
    if (DOCA_IS_ERROR(rc)) {
        return_doca_buf(rx_doca_buf);
        PRINT_DOCA_ERR(hwqrx_logerr, rc, "doca_eth_rxq_task_recv_allocate_init");
        return false;
    }

    --m_rxq_task_debt; // Must be set before return_doca_task()
    rc = doca_task_submit_ex(doca_eth_rxq_task_recv_as_doca_task(rx_doca_task), task_flag);
    if (DOCA_IS_ERROR(rc)) {
        return_doca_task(rx_doca_task);
        PRINT_DOCA_ERR(hwqrx_logerr, rc, "doca_eth_rxq_task_recv_as_doca_task");
        return false;
    }

    buff->clear_transport_data();
    m_rx_pool.pop_front();
    return true;
}

bool hw_queue_rx::fill_buffers_from_global_pool()
{
    size_t more_bufs =
        (m_rxq_task_debt > m_rx_pool.size() ? m_rxq_task_debt - m_rx_pool.size() : 0U);

    if (more_bufs) {
        hwqrx_logfunc("Allocating additional %d buffers for internal use", more_bufs);

        // Assume locked!
        // Add an additional free buffer descs to RX cq mgr
        if (!g_buffer_pool_rx_rwqe->get_buffers_thread_safe(m_rx_pool, m_p_ring, more_bufs, 0)) {
            return false;
        }
    }

    // TODO DOCA: Add Statistics
    // m_p_cq_stat->n_buffer_pool_len = m_rx_pool.size();
    return true;
}

void hw_queue_rx::return_doca_buf(doca_buf *buf)
{
    doca_error_t rc_state = doca_buf_dec_refcount(buf, nullptr);
    if (unlikely(rc_state != DOCA_SUCCESS)) {
        PRINT_DOCA_ERR(hwqrx_logerr, rc_state, "doca_buf_dec_refcount");
    }
}

/*void hw_queue_rx::callback_rxq_state_changed(
    const union doca_data user_data, struct doca_ctx *ctx,
    enum doca_ctx_states prev_state,  enum doca_ctx_states next_state)
{
    hw_queue_rx *hw_rxq = reinterpret_cast<hw_queue_rx *>(user_data.ptr);
    if (DOCA_CTX_STATE_IDLE == next_state) {
        hw_rxq-
    }
}*/

void hw_queue_rx::start_doca_rxq()
{
    hwqrx_logdbg("Starting DOCA RXQ: %p pid: %d", m_doca_rxq.get(), getpid());

    if (!m_p_ib_ctx_handler->get_doca_flow_port()) {
        hwqrx_logerr("modify_queue_to_ready_state unable to get DOCA flow port, RXQ: %p", this);
    }

    doca_error_t err = doca_ctx_start(m_doca_ctx_rxq);
    if (DOCA_IS_ERROR(err)) {
        PRINT_DOCA_ERR(hwqrx_logerr, err, "doca_ctx_start(RXQ). RXQ:%p", m_doca_rxq.get());
    }

    hwqrx_loginfo("DOCA RXQ started, ctx: %p", m_doca_ctx_rxq);

    err = doca_eth_rxq_get_flow_queue_id(m_doca_rxq.get(), &m_doca_rx_queue_id);
    if (DOCA_IS_ERROR(err)) {
        PRINT_DOCA_ERR(hwqrx_logerr, err, "doca_eth_rxq_get_flow_queue_id. RXQ:%p",
                       m_doca_rxq.get());
    }

    submit_rxq_tasks();
}

void hw_queue_rx::stop_doca_rxq()
{
    hwqrx_logdbg("Stopping DOCA RXQ: %p", m_doca_rxq.get());

    doca_error_t err = doca_ctx_stop(m_doca_ctx_rxq);
    if (DOCA_ERROR_IN_PROGRESS == err) {
        doca_ctx_states ctx_state = DOCA_CTX_STATE_STOPPING; // Just to enter the while loop.
        while (DOCA_CTX_STATE_IDLE != ctx_state) {
            if (!doca_pe_progress(m_doca_pe.get())) {
                err = doca_ctx_get_state(m_doca_ctx_rxq, &ctx_state);
                if (err != DOCA_SUCCESS) {
                    PRINT_DOCA_ERR(hwqrx_logerr, err,
                                   "Error flushing DOCA RXQ (doca_ctx_get_state). RXQ:%p",
                                   m_doca_rxq.get());
                    break;
                }
            }
        }
    } else if (DOCA_IS_ERROR(err)) {
        PRINT_DOCA_ERR(hwqrx_logerr, err, "doca_ctx_stop(RXQ). RXQ:%p", m_doca_rxq.get());
    }
}

void hw_queue_rx::destory_doca_rxq(doca_eth_rxq *rxq)
{
    doca_error_t err = doca_eth_rxq_destroy(rxq);
    if (DOCA_IS_ERROR(err)) {
        PRINT_DOCA_ERR(__log_err, err, "doca_eth_rxq_destroy rxq: %p", rxq);
    }
}

void hw_queue_rx::destory_doca_inventory(doca_buf_inventory *inv)
{
    doca_error_t err = doca_buf_inventory_destroy(inv);
    if (DOCA_IS_ERROR(err)) {
        PRINT_DOCA_ERR(__log_err, err, "doca_buf_inventory_destroy Inv: %p", inv);
    }
}

void hw_queue_rx::destory_doca_pe(doca_pe *pe)
{
    doca_error_t err = doca_pe_destroy(pe);
    if (DOCA_IS_ERROR(err)) {
        PRINT_DOCA_ERR(__log_err, err, "doca_pe_destroy PE: %p", pe);
    }
}

void hw_queue_rx::return_doca_task(doca_eth_rxq_task_recv *task_recv)
{
    doca_buf *buf = nullptr;
    doca_error_t err = doca_eth_rxq_task_recv_get_pkt(task_recv, &buf);
    if (unlikely(DOCA_IS_ERROR(err))) {
        PRINT_DOCA_ERR(hwqrx_logerr, err, "doca_eth_rxq_task_recv_get_pkt");
    } else {
        return_doca_buf(buf);
    }

    doca_task_free(doca_eth_rxq_task_recv_as_doca_task(task_recv));
    ++m_rxq_task_debt;
}

void hw_queue_rx::reclaim_rx_buffer_chain_loop(mem_buf_desc_t *buff)
{
    // TODO DOCA: Remove usage of lwip_pbuf.ref for RX
    if (buff->dec_ref_count() <= 1 && (buff->lwip_pbuf.ref-- <= 1)) {
        mem_buf_desc_t *temp = nullptr;
        while (buff) {
            buff->p_desc_owner = m_p_ring; // In case socket switched rings.
            temp = buff;
            assert(temp->lwip_pbuf.type != PBUF_ZEROCOPY);
            buff = temp->p_next_desc;
            temp->p_next_desc = nullptr;
            temp->p_prev_desc = nullptr;
            temp->reset_ref_count();
            free_lwip_pbuf(&temp->lwip_pbuf);
            m_rx_pool.push_front(temp);
        }
        // m_p_cq_stat->n_buffer_pool_len = m_rx_pool.size();
    } else if (buff->lwip_pbuf.ref != (unsigned int)buff->get_ref_count()) {
        hwqrx_logwarn("Uneven lwip.ref and buf.ref %u,%d", buff->lwip_pbuf.ref,
                      buff->get_ref_count());
    }
}

void hw_queue_rx::reclaim_rx_buffer_chain(mem_buf_desc_t *buff_chain)
{
    reclaim_rx_buffer_chain_loop(buff_chain);
    post_reclaim_fill();
}

void hw_queue_rx::reclaim_rx_buffer_chain_queue(descq_t *buff_list)
{
    while (!buff_list->empty()) {
        reclaim_rx_buffer_chain_loop(buff_list->get_and_pop_front());
    }

    post_reclaim_fill();
}

void hw_queue_rx::post_reclaim_fill()
{
    if (unlikely(m_rxq_task_debt > m_rx_debt_submit_treshold)) {
        submit_rxq_tasks();
    }

    return_extra_buffers();
}

void hw_queue_rx::return_extra_buffers()
{
    // Use integers for percents calculations to avoid floating point operations.
    if (unlikely(m_rx_pool.size() > m_rx_buff_pool_treshold_max)) {
        size_t return_buffs_num = m_rx_pool.size() - m_rx_buff_pool_treshold_min;

        hwqrx_logfunc("Returning %zu buffers to global RX pool", return_buffs_num);
        g_buffer_pool_rx_rwqe->put_buffers_thread_safe(&m_rx_pool, return_buffs_num);
        // m_p_cq_stat->n_buffer_pool_len = m_rx_pool.size();
    }
}

void hw_queue_rx::rx_task_completion_cb(doca_eth_rxq_task_recv *task_recv, doca_data task_user_data,
                                        doca_data ctx_user_data)
{
    mem_buf_desc_t *mem_buf = reinterpret_cast<mem_buf_desc_t *>(task_user_data.ptr);
    hw_queue_rx *hw_rx = reinterpret_cast<hw_queue_rx *>(ctx_user_data.ptr);
    doca_buf *buf = nullptr;
    doca_error_t rc = doca_eth_rxq_task_recv_get_pkt(task_recv, &buf);
    if (unlikely(DOCA_IS_ERROR(rc))) {
        PRINT_DOCA_ERR(__log_err, rc, "doca_eth_rxq_task_recv_get_pkt");
        rx_task_error_cb(task_recv, task_user_data, ctx_user_data);
        return;
    }

    uint8_t l3ok = 0U;
    uint8_t l4ok = 0U;
    rc = doca_buf_get_data_len(buf, &mem_buf->sz_data);
    doca_error_t rc3 = doca_eth_rxq_task_recv_get_l3_ok(task_recv, &l3ok);
    doca_error_t rc4 = doca_eth_rxq_task_recv_get_l4_ok(task_recv, &l4ok);
    if (unlikely(DOCA_IS_ERROR(rc) || DOCA_IS_ERROR(rc3) || DOCA_IS_ERROR(rc4))) {
        __log_err("rx_task_completion_cb, task_recv: %p, buf: %p, rc/rc3/rc4: %d/%d/%d", task_recv,
                  buf, static_cast<int>(rc), static_cast<int>(rc3), static_cast<int>(rc4));
        rx_task_error_cb(task_recv, task_user_data, ctx_user_data);
        return;
    }

    mem_buf->rx.is_sw_csum_need = (l3ok == 0U || l4ok == 0);

    hw_rx->return_doca_task(task_recv);
    hw_rx->m_polled_buf = mem_buf;

    __log_func("rx_task_completion_cb pid: %d\n", (int)getpid());
}

void hw_queue_rx::rx_task_error_cb(doca_eth_rxq_task_recv *task_recv, doca_data task_user_data,
                                   doca_data ctx_user_data)
{
    mem_buf_desc_t *mem_buf = reinterpret_cast<mem_buf_desc_t *>(task_user_data.ptr);
    hw_queue_rx *hw_rx = reinterpret_cast<hw_queue_rx *>(ctx_user_data.ptr);
    doca_ctx_states ctx_state = DOCA_CTX_STATE_STOPPING;
    doca_error_t rc_state = doca_ctx_get_state(hw_rx->m_doca_ctx_rxq, &ctx_state);
    ctx_state = ((ctx_state != DOCA_CTX_STATE_IDLE) ? ctx_state : DOCA_CTX_STATE_STOPPING);
    if (rc_state != DOCA_SUCCESS || ctx_state != DOCA_CTX_STATE_STOPPING) {
        PRINT_DOCA_ERR(__log_err,
                       doca_task_get_status(doca_eth_rxq_task_recv_as_doca_task(task_recv)),
                       "RX Task Error");
        // TODO DOCA: Add statistics for errors
    }

    __log_func("rx_task_error_cb, task_recv: %p, rc_state: %d, ctx_state: %d", task_recv, rc_state,
               ctx_state);

    hw_rx->return_doca_task(task_recv);
    hw_rx->reclaim_rx_buffer_chain_loop(mem_buf);
    hw_rx->m_polled_buf = nullptr;
}

bool hw_queue_rx::poll_and_process_rx()
{
    hwqrx_logfunc("");

    // DOCA forbides calling doca_pe_progress on armed PE.
    if (unlikely(m_notification_armed)) {
        // hwqrx_logwarn("Poll attempt on armed PE. hw_queue_rx: %p", this);
        // Armed PE context is suspended inside DOCA until event arrives. No way to poll.
        return true;
    }

    uint32_t rx_polled = 0U;
    while (rx_polled < safe_mce_sys().cq_poll_batch_max && doca_pe_progress(m_doca_pe.get())) {
        if (likely(m_polled_buf)) { // The doca_pe_progress returns 1 for error-progress as well.
            process_recv_buffer(m_polled_buf);
            ++rx_polled;
        }
    }

    m_p_ring->m_gro_mgr.flush_all(nullptr);

    submit_rxq_tasks();

    return (rx_polled < safe_mce_sys().cq_poll_batch_max);
}

void hw_queue_rx::process_recv_buffer(mem_buf_desc_t *p_mem_buf_desc)
{
    if (!m_p_ring->rx_process_buffer(p_mem_buf_desc, nullptr)) {
        // If buffer is dropped by callback - return to RX pool
        reclaim_rx_buffer_chain_loop(p_mem_buf_desc);
    }
}

bool hw_queue_rx::request_notification()
{
    if (likely(!m_notification_armed)) {
        doca_error_t rc = doca_pe_request_notification(m_doca_pe.get());
        if (unlikely(DOCA_IS_ERROR(rc))) {
            PRINT_DOCA_ERR(hwqrx_logerr, rc, "doca_pe_request_notification");
            return false;
        }
    }

    hwqrx_logfunc("Requested notification hw_queue_rx: %p", this);
    m_notification_armed = true;
    return true;
}

void hw_queue_rx::clear_notification()
{
    if (m_notification_armed) {
        m_notification_armed = false;
        doca_error_t rc = doca_pe_clear_notification(m_doca_pe.get(), m_notification_handle);
        if (unlikely(DOCA_IS_ERROR(rc))) {
            PRINT_DOCA_ERR(hwqrx_logerr, rc, "doca_pe_clear_notification");
        }
    } else {
        hwqrx_logwarn("Clear notification attempt on unarmed PE. hw_queue_rx: %p", this);
    }
}

void hw_queue_rx::modify_moderation(uint16_t period_usec, uint16_t comp_count)
{
    doca_error_t rc =
        doca_eth_rxq_set_notification_moderation(m_doca_rxq.get(), period_usec, comp_count);
    if (unlikely(DOCA_IS_ERROR(rc))) {
        PRINT_DOCA_ERR(hwqrx_logerr, rc, "doca_eth_rxq_set_notification_moderation");
    }
}

// DPCP Implementation ---------------------------------------------------

bool hw_queue_rx::configure_rq(ibv_comp_channel *rx_comp_event_channel)
{
    // Create associated cq_mgr_tx
    BULLSEYE_EXCLUDE_BLOCK_START
    m_p_cq_mgr_rx = init_rx_cq_mgr(rx_comp_event_channel);
    if (!m_p_cq_mgr_rx) {
        hwqrx_logerr("Failed allocating m_p_cq_mgr_rx (errno=%d %m)", errno);
        return false;
    }
    BULLSEYE_EXCLUDE_BLOCK_END

    // Modify the cq_mgr_rx to use a non-blocking event channel
    set_fd_block_mode(m_p_cq_mgr_rx->get_channel_fd(), false);

    m_curr_rx_wr = 0;

    xlio_ib_mlx5_cq_t mlx5_cq;
    memset(&mlx5_cq, 0, sizeof(mlx5_cq));
    xlio_ib_mlx5_get_cq(m_p_cq_mgr_rx->get_ibv_cq_hndl(), &mlx5_cq);

    if (safe_mce_sys().enable_striding_rq) {
        m_rx_sge = 2U; // Striding-RQ needs a reserved segment.
        m_strq_wqe_reserved_seg = 1U;
    }

    m_ibv_rx_wr_array = new ibv_recv_wr[m_n_sysvar_rx_num_wr_to_post_recv];
    m_ibv_rx_sg_array = new ibv_sge[m_n_sysvar_rx_num_wr_to_post_recv * m_rx_sge];

    for (uint32_t wr_idx = 0; wr_idx < m_n_sysvar_rx_num_wr_to_post_recv; wr_idx++) {
        m_ibv_rx_wr_array[wr_idx].sg_list = &m_ibv_rx_sg_array[wr_idx * m_rx_sge];
        m_ibv_rx_wr_array[wr_idx].num_sge = m_rx_sge;
        m_ibv_rx_wr_array[wr_idx].next = &m_ibv_rx_wr_array[wr_idx + 1];
    }

    m_ibv_rx_wr_array[m_n_sysvar_rx_num_wr_to_post_recv - 1].next = nullptr;

    if (safe_mce_sys().enable_striding_rq) {
        for (uint32_t wr_idx = 0; wr_idx < m_n_sysvar_rx_num_wr_to_post_recv; wr_idx++) {
            memset(m_ibv_rx_wr_array[wr_idx].sg_list, 0, sizeof(ibv_sge));
            // To bypass a check inside xlio_ib_mlx5_post_recv.
            m_ibv_rx_wr_array[wr_idx].sg_list[0].length = 1U;
        }
    }

    // Create the QP
    if (!prepare_rq(mlx5_cq.cq_num)) {
        return false;
    }

    return true;
}

void hw_queue_rx::up()
{
    start_doca_rxq();

    m_tir.reset(create_tir());
    if (!m_tir) {
        hwqrx_logpanic("TIR creation for hw_queue_rx failed (errno=%d %m)", errno);
    }

    release_rx_buffers(); // We might have old flushed cqe's in our CQ still from previous HA event

    modify_queue_to_ready_state();

    m_p_cq_mgr_rx->add_hqrx(this);
}

void hw_queue_rx::down()
{
    stop_doca_rxq();

    m_tir.reset(nullptr);

    modify_queue_to_error_state();

    // let the QP drain all wqe's to flushed cqe's now that we moved
    // it to error state and post_sent final trigger for completion
    usleep(1000);

    release_rx_buffers();
    m_p_cq_mgr_rx->del_hqrx(this);
}

void hw_queue_rx::release_rx_buffers()
{
    int total_ret = m_curr_rx_wr;
    if (m_curr_rx_wr) {
        hwqrx_logdbg("Returning %d pending post_recv buffers to CQ owner", m_curr_rx_wr);
        while (m_curr_rx_wr) {
            // Cleaning unposted buffers. Unposted buffers are not attached to any strides.
            --m_curr_rx_wr;
            mem_buf_desc_t *p_mem_buf_desc =
                (mem_buf_desc_t *)(uintptr_t)m_ibv_rx_wr_array[m_curr_rx_wr].wr_id;
            if (p_mem_buf_desc && p_mem_buf_desc->p_desc_owner) {
                m_p_ring->mem_buf_desc_return_to_owner_rx(p_mem_buf_desc);
            } else {
                g_buffer_pool_rx_rwqe->put_buffers_thread_safe(p_mem_buf_desc);
            }
        }
    }
    // Wait for all FLUSHed WQE on Rx CQ
    hwqrx_logdbg("draining cq_mgr_rx %p (last_posted_rx_wr_id = %lu)", m_p_cq_mgr_rx,
                 m_last_posted_rx_wr_id);
    uintptr_t last_polled_rx_wr_id = 0;
    while (m_p_cq_mgr_rx && last_polled_rx_wr_id != m_last_posted_rx_wr_id && errno != EIO &&
           !is_rq_empty() && !m_p_ib_ctx_handler->is_removed()) {

        // Process the FLUSH'ed WQE's
        int ret = m_p_cq_mgr_rx->drain_and_proccess(&last_polled_rx_wr_id);
        hwqrx_logdbg("draining completed on cq_mgr_rx (%d wce) last_polled_rx_wr_id = %lu", ret,
                     last_polled_rx_wr_id);

        total_ret += ret;

        if (!ret) {
            // Query context for ib_verbs events (especially for IBV_EVENT_DEVICE_FATAL)
            g_p_event_handler_manager->query_for_ibverbs_event(
                m_p_ib_ctx_handler->get_ibv_context()->async_fd);
        }

        // Add short delay (500 usec) to allow for WQE's to be flushed to CQ every poll cycle
        const struct timespec short_sleep = {0, 500000}; // 500 usec
        nanosleep(&short_sleep, nullptr);
    }
    m_last_posted_rx_wr_id = 0; // Clear the posted WR_ID flag, we just clear the entire RQ
    hwqrx_logdbg("draining completed with a total of %d wce's on cq_mgr_rx", total_ret);
    NOT_IN_USE(total_ret); // Suppress --enable-opt-log=high warning
}

void hw_queue_rx::post_recv_buffers(descq_t *p_buffers, size_t count)
{
    hwqrx_logfuncall("");
    // Called from cq_mgr_rx context under cq_mgr_rx::LOCK!
    while (count--) {
        post_recv_buffer(p_buffers->get_and_pop_front());
    }
}

void hw_queue_rx::modify_queue_to_ready_state()
{
    hwqrx_logdbg("");
    dpcp::status rc = m_rq->modify_state(dpcp::RQ_RDY);
    if (dpcp::DPCP_OK != rc) {
        hwqrx_logerr("Failed to modify rq state to RDY, rc: %d, rqn: %" PRIu32,
                     static_cast<int>(rc), m_rq_data.rqn);
    }
}

void hw_queue_rx::modify_queue_to_error_state()
{
    hwqrx_logdbg("");

    m_p_cq_mgr_rx->clean_cq();

    dpcp::status rc = m_rq->modify_state(dpcp::RQ_ERR);

    /* During plugout theres is possibility that kernel
     * remove device resources before working process complete
     * removing process. As a result ibv api function can
     * return EIO=5 errno code.
     */
    if (dpcp::DPCP_OK != rc && errno != EIO) {
        hwqrx_logerr("Failed to modify rq state to ERR, rc: %d, rqn: %" PRIu32,
                     static_cast<int>(rc), m_rq_data.rqn);
    }
}

rfs_rule *hw_queue_rx::create_rfs_rule(doca_flow_match &match_val, doca_flow_match &match_msk,
                                       dpcp::match_params &match_value,
                                       dpcp::match_params &match_mask, uint16_t priority,
                                       uint32_t flow_tag, xlio_tir *tir_ext)
{
    if (m_p_ib_ctx_handler && m_p_ib_ctx_handler->get_dpcp_adapter()) {
        // TLS RX uses tir_ext.
        dpcp::tir *dpcp_tir = (tir_ext ? xlio_tir_to_dpcp_tir(tir_ext) : m_tir.get());
        uint16_t rxq_id = m_doca_rx_queue_id; // TODO: Add Support for TLS-RX.

        std::unique_ptr<rfs_rule> new_rule(new rfs_rule());
        if (dpcp_tir && m_doca_rx_queue_id &&
            new_rule->create(match_val, match_msk, rxq_id, match_value, match_mask, *dpcp_tir,
                             priority, flow_tag, *m_p_ib_ctx_handler)) {
            return new_rule.release();
        }
    }

    return nullptr;
}

void hw_queue_rx::post_recv_buffer(mem_buf_desc_t *p_mem_buf_desc)
{
    uint32_t index = (m_curr_rx_wr * m_rx_sge) + m_strq_wqe_reserved_seg;
    m_ibv_rx_sg_array[index].addr = (uintptr_t)p_mem_buf_desc->p_buffer;
    m_ibv_rx_sg_array[index].length = p_mem_buf_desc->sz_buffer;
    m_ibv_rx_sg_array[index].lkey = p_mem_buf_desc->lkey;

    post_recv_buffer_rq(p_mem_buf_desc);
}

void hw_queue_rx::post_recv_buffer_rq(mem_buf_desc_t *p_mem_buf_desc)
{
    if (m_n_sysvar_rx_prefetch_bytes_before_poll) {
        if (m_p_prev_rx_desc_pushed) {
            m_p_prev_rx_desc_pushed->p_prev_desc = p_mem_buf_desc;
        }
        m_p_prev_rx_desc_pushed = p_mem_buf_desc;
    }

    m_ibv_rx_wr_array[m_curr_rx_wr].wr_id = (uintptr_t)p_mem_buf_desc;

    if (m_rq_wqe_idx_to_wrid) {
        uint32_t index = m_rq_wqe_counter & (m_rx_num_wr - 1);
        m_rq_wqe_idx_to_wrid[index] = (uintptr_t)p_mem_buf_desc;
        ++m_rq_wqe_counter;
    }

    if (m_curr_rx_wr == m_n_sysvar_rx_num_wr_to_post_recv - 1) {

        m_last_posted_rx_wr_id = (uintptr_t)p_mem_buf_desc;

        m_p_prev_rx_desc_pushed = nullptr;
        p_mem_buf_desc->p_prev_desc = nullptr;

        m_curr_rx_wr = 0;
        struct ibv_recv_wr *bad_wr = nullptr;
        if (xlio_raw_post_recv(&bad_wr) < 0) {
            uint32_t n_pos_bad_rx_wr =
                ((uint8_t *)bad_wr - (uint8_t *)m_ibv_rx_wr_array) / sizeof(struct ibv_recv_wr);
            hwqrx_logerr("failed posting list (errno=%d %s)", errno, strerror(errno));
            hwqrx_logerr(
                "bad_wr is %d in submitted list (bad_wr=%p, m_ibv_rx_wr_array=%p, size=%zu)",
                n_pos_bad_rx_wr, bad_wr, m_ibv_rx_wr_array, sizeof(struct ibv_recv_wr));
            hwqrx_logerr("bad_wr info: wr_id=%#lx, next=%p, addr=%#lx, length=%d, lkey=%#x",
                         bad_wr[0].wr_id, bad_wr[0].next, bad_wr[0].sg_list[0].addr,
                         bad_wr[0].sg_list[0].length, bad_wr[0].sg_list[0].lkey);

            // Fix broken linked list of rx_wr
            if (n_pos_bad_rx_wr != (m_n_sysvar_rx_num_wr_to_post_recv - 1)) {
                m_ibv_rx_wr_array[n_pos_bad_rx_wr].next = &m_ibv_rx_wr_array[n_pos_bad_rx_wr + 1];
            }
            throw_xlio_exception("Failed to post a WQE to RQ");
        }
        hwqrx_logfunc("Successful buffer post to RQ");
    } else {
        m_curr_rx_wr++;
    }
}

int hw_queue_rx::xlio_raw_post_recv(struct ibv_recv_wr **bad_wr)
{
    struct mlx5_wqe_data_seg *scat;
    int err = 0;
    int nreq = 0;
    int i, j;
    int ind = m_rq_data.head & (m_rq_data.wqe_cnt - 1);

    struct ibv_recv_wr *wr = m_ibv_rx_wr_array;
    for (; wr; ++nreq, wr = wr->next) {
        if (unlikely((int)m_rq_data.head - (int)m_rq_data.tail + nreq >= (int)m_rx_num_wr)) {
            errno = ENOMEM;
            err = -1;
            *bad_wr = wr;
            goto out;
        }

        if (unlikely(wr->num_sge > (int)m_rx_sge)) {
            errno = EINVAL;
            err = -1;
            *bad_wr = wr;
            goto out;
        }

        scat =
            (struct mlx5_wqe_data_seg *)((uint8_t *)m_rq_data.buf + (ind << m_rq_data.wqe_shift));

        for (i = 0, j = 0; i < wr->num_sge; ++i) {
            if (unlikely(!wr->sg_list[i].length)) {
                continue;
            }

            scat[j].byte_count = htonl(wr->sg_list[i].length);
            scat[j].lkey = htonl(wr->sg_list[i].lkey);
            scat[j].addr = htonll(wr->sg_list[i].addr);
            j++;
        }

        if (j < (int)m_rx_sge) {
            scat[j].byte_count = 0;
            scat[j].lkey = htonl(MLX5_INVALID_LKEY);
            scat[j].addr = 0;
        }

        ind = (ind + 1) & (m_rq_data.wqe_cnt - 1);
    }

out:
    if (likely(nreq)) {
        m_rq_data.head += nreq;

        wmb(); // Make sure that descriptors are written before doorbell record.

        // Buffers are posted only after the RQ is in ready state. OK to update doorbell.
        *m_rq_data.dbrec = htonl(m_rq_data.head & 0xffff);
    }

    return err;
}

cq_mgr_rx *hw_queue_rx::init_rx_cq_mgr(struct ibv_comp_channel *p_rx_comp_event_channel)
{
    if (safe_mce_sys().enable_striding_rq) {
        return new cq_mgr_rx_strq(m_p_ring, m_p_ib_ctx_handler,
                                  safe_mce_sys().strq_stride_num_per_rwqe * m_rx_num_wr,
                                  safe_mce_sys().strq_stride_size_bytes,
                                  safe_mce_sys().strq_stride_num_per_rwqe, p_rx_comp_event_channel);
    }

    return new cq_mgr_rx_regrq(m_p_ring, m_p_ib_ctx_handler, m_rx_num_wr, p_rx_comp_event_channel);
}

#if defined(DEFINED_UTLS)
xlio_tir *hw_queue_rx::tls_create_tir(bool cached)
{
    xlio_tir *tir = NULL;

    if (cached && !m_tls_tir_cache.empty()) {
        tir = m_tls_tir_cache.back();
        m_tls_tir_cache.pop_back();
    } else if (!cached) {
        dpcp::tir *new_tir = create_tir(true);

        if (new_tir != NULL) {
            tir = new xlio_tir(this, new_tir, xlio_ti::ti_type::TLS_TIR);
        }
        if (unlikely(tir == NULL && new_tir != NULL)) {
            delete new_tir;
        }
    }
    return tir;
}

void hw_queue_rx::tls_release_tir(xlio_tir *tir)
{
    /* TODO We don't have to lock ring to destroy DEK object (a garbage collector?). */

    assert(tir && tir->m_type == xlio_ti::ti_type::TLS_TIR);
    tir->m_released = true;
    tir->assign_callback(NULL, NULL);
    if (tir->m_ref == 0) {
        put_tls_tir_in_cache(tir);
    }
}

void hw_queue_rx::put_tls_tir_in_cache(xlio_tir *tir)
{
    // Because the absense of TIR flush command, reusing a TIR
    // may result in undefined behaviour.
    // Until a flush command is available the TIR cache is disabled.
    // Re-enabling TIR cache should also add destroy_tir_cache on ring cleanup.
    // m_tls_tir_cache.push_back(tir);

    delete tir;
}

void hw_queue_rx::ti_released(xlio_ti *ti)
{
    assert(ti->m_released);
    assert(ti->m_ref == 0);
    if (ti->m_type == xlio_ti::ti_type::TLS_TIR) {
        put_tls_tir_in_cache(static_cast<xlio_tir *>(ti));
    }
}
#else /* DEFINED_UTLS */
void hw_queue_rx::ti_released(xlio_ti *) {};
#endif /* defined(DEFINED_UTLS) */

dpcp::tir *hw_queue_rx::create_tir(bool is_tls /*=false*/)
{
    dpcp::tir *tir_obj = nullptr;
    dpcp::status status = dpcp::DPCP_OK;
    dpcp::tir::attr tir_attr;

    memset(&tir_attr, 0, sizeof(tir_attr));
    tir_attr.flags = dpcp::TIR_ATTR_INLINE_RQN | dpcp::TIR_ATTR_TRANSPORT_DOMAIN;
    tir_attr.inline_rqn = m_rq_data.rqn;
    tir_attr.transport_domain = m_p_ib_ctx_handler->get_dpcp_adapter()->get_td();

    if (m_p_ring->m_lro.cap && m_p_ring->m_lro.max_payload_sz) {
        tir_attr.flags |= dpcp::TIR_ATTR_LRO;
        tir_attr.lro.timeout_period_usecs = XLIO_MLX5_PARAMS_LRO_TIMEOUT;
        tir_attr.lro.enable_mask = 3; // Bitmask for IPv4 and IPv6 support
        tir_attr.lro.max_msg_sz = m_p_ring->m_lro.max_payload_sz >> 8;
    }

    if (is_tls) {
        tir_attr.flags |= dpcp::TIR_ATTR_TLS;
        tir_attr.tls_en = 1;
    }

    status = m_p_ib_ctx_handler->get_dpcp_adapter()->create_tir(tir_attr, tir_obj);

    if (dpcp::DPCP_OK != status) {
        hwqrx_logerr("Failed creating dpcp tir with flags=0x%x status=%d", tir_attr.flags, status);
        return nullptr;
    }

    hwqrx_logdbg("TIR: %p created", tir_obj);

    return tir_obj;
}

bool hw_queue_rx::prepare_rq(uint32_t cqn)
{
    hwqrx_logdbg("");

    dpcp::adapter *dpcp_adapter = m_p_ib_ctx_handler->get_dpcp_adapter();
    if (!dpcp_adapter) {
        hwqrx_logerr("Failed to get dpcp::adapter for prepare_rq");
        return false;
    }

    // user_index Unused.
    dpcp::rq_attr rqattrs;
    memset(&rqattrs, 0, sizeof(rqattrs));
    rqattrs.cqn = cqn;
    rqattrs.wqe_num = m_rx_num_wr;
    rqattrs.wqe_sz = m_rx_sge;

    if (safe_mce_sys().hw_ts_conversion_mode == TS_CONVERSION_MODE_RTC) {
        hwqrx_logdbg("Enabled RTC timestamp format for RQ");
        rqattrs.ts_format = dpcp::rq_ts_format::RQ_TS_REAL_TIME;
    }

    std::unique_ptr<dpcp::basic_rq> new_rq;
    dpcp::status rc = dpcp::DPCP_OK;

    if (safe_mce_sys().enable_striding_rq) {
        rqattrs.buf_stride_sz = safe_mce_sys().strq_stride_size_bytes;
        rqattrs.buf_stride_num = safe_mce_sys().strq_stride_num_per_rwqe;

        // Striding-RQ WQE format is as of Shared-RQ (PRM, page 381, wq_type).
        // In this case the WQE minimum size is 2 * 16, and the first segment is reserved.
        rqattrs.wqe_sz = m_rx_sge * 16U;

        dpcp::striding_rq *new_rq_ptr = nullptr;
        rc = dpcp_adapter->create_striding_rq(rqattrs, new_rq_ptr);
        new_rq.reset(new_rq_ptr);
    } else {
        dpcp::regular_rq *new_rq_ptr = nullptr;
        rc = dpcp_adapter->create_regular_rq(rqattrs, new_rq_ptr);
        new_rq.reset(new_rq_ptr);
    }

    if (dpcp::DPCP_OK != rc) {
        hwqrx_logerr("Failed to create dpcp rq, rc: %d, cqn: %" PRIu32, static_cast<int>(rc), cqn);
        return false;
    }

    if (!store_rq_mlx5_params(*new_rq)) {
        hwqrx_logerr(
            "Failed to retrieve initial DPCP RQ parameters, rc: %d, basic_rq: %p, cqn: %" PRIu32,
            static_cast<int>(rc), new_rq.get(), cqn);
        return false;
    }

    m_rq = std::move(new_rq);

    m_rq_wqe_idx_to_wrid =
        (uint64_t *)mmap(nullptr, m_rx_num_wr * sizeof(*m_rq_wqe_idx_to_wrid),
                         PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
    if (m_rq_wqe_idx_to_wrid == MAP_FAILED) {
        hwqrx_logerr("Failed allocating m_rq_wqe_idx_to_wrid (errno=%d %m)", errno);
        return false;
    }

    // At this stage there is no TIR associated with the RQ, So it mimics QP INIT state.
    // At RDY state without a TIR, Work Requests can be submitted to the RQ.
    modify_queue_to_ready_state();

    hwqrx_logdbg("Succeeded to create dpcp rq, rqn: %" PRIu32 ", cqn: %" PRIu32, m_rq_data.rqn,
                 cqn);

    return true;
}

bool hw_queue_rx::store_rq_mlx5_params(dpcp::basic_rq &new_rq)
{
    uint32_t *dbrec_tmp = nullptr;
    dpcp::status rc = new_rq.get_dbrec(dbrec_tmp);
    if (dpcp::DPCP_OK != rc) {
        hwqrx_logerr("Failed to retrieve dbrec of dpcp rq, rc: %d, basic_rq: %p",
                     static_cast<int>(rc), &new_rq);
        return false;
    }
    m_rq_data.dbrec = dbrec_tmp;

    rc = new_rq.get_wq_buf(m_rq_data.buf);
    if (dpcp::DPCP_OK != rc) {
        hwqrx_logerr("Failed to retrieve wq-buf of dpcp rq, rc: %d, basic_rq: %p",
                     static_cast<int>(rc), &new_rq);
        return false;
    }

    rc = new_rq.get_id(m_rq_data.rqn);
    if (dpcp::DPCP_OK != rc) {
        hwqrx_logerr("Failed to retrieve rqn of dpcp rq, rc: %d, basic_rq: %p",
                     static_cast<int>(rc), &new_rq);
        return false;
    }

    new_rq.get_wqe_num(m_rq_data.wqe_cnt);
    new_rq.get_wq_stride_sz(m_rq_data.stride);
    if (safe_mce_sys().enable_striding_rq) {
        m_rq_data.stride /= 16U;
    }

    m_rq_data.wqe_shift = ilog_2(m_rq_data.stride);
    m_rq_data.head = 0;
    m_rq_data.tail = 0;

    return true;
}
