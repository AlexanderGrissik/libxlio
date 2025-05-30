/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#ifndef NEIGHBOUR_H
#define NEIGHBOUR_H

#include <rdma/rdma_cma.h>

#include "state_machine/sm.h"
#include "core/util/sys_vars.h"
#include "core/infra/cache_subject_observer.h"
#include "core/infra/sender.h"
#include "core/event/event_handler_ibverbs.h"
#include "core/event/event_handler_rdma_cm.h"
#include "core/event/event_handler_manager.h"
#include "core/event/timer_handler.h"
#include "core/event/netlink_event.h"
#include "core/util/ip_address.h"
#include "core/proto/L2_address.h"

#include "core/proto/header.h"
#include "core/dev/ring_allocation_logic.h"
#include "core/dev/net_device_val.h"
#include "core/dev/ring.h"
#include "core/proto/arp.h"

class neigh_key {
public:
    neigh_key(ip_addr addr, net_device_val *p_ndvl)
        : m_ip_addrs(std::move(addr))
        , m_p_net_dev_val(p_ndvl) {};
    virtual ~neigh_key() {};

    const std::string to_str() const
    {
        return (m_ip_addrs.to_str() + " " + m_p_net_dev_val->to_str());
    }

    const ip_addr &get_ip_addr() const { return m_ip_addrs; };
    net_device_val *get_net_device_val() const { return m_p_net_dev_val; };

    virtual size_t hash(void)
    {
        uint8_t csum = 0;
        uint8_t *pval = (uint8_t *)this;
        for (size_t i = 0; i < sizeof(ip_address); ++i, ++pval) {
            csum ^= *pval;
        }
        return csum;
    }

    virtual bool operator==(neigh_key const &other) const
    {
        return ((m_ip_addrs == other.m_ip_addrs) && (m_p_net_dev_val == other.m_p_net_dev_val));
    }

private:
    ip_addr m_ip_addrs;
    net_device_val *m_p_net_dev_val;
};

inline std::string to_string_val(const neigh_key &k)
{
    return k.to_str();
}

namespace std {
template <> class hash<neigh_key> {
public:
    size_t operator()(const neigh_key &key) const
    {
        neigh_key *tmp_key = (neigh_key *)&key;
        return tmp_key->hash();
    }
};
} // namespace std

class neigh_val {
public:
    neigh_val()
        : m_trans_type(XLIO_TRANSPORT_UNKNOWN)
        , m_l2_address(nullptr) {};
    virtual ~neigh_val() {};

    virtual void zero_all_members()
    {
        if (m_l2_address) {
            delete m_l2_address;
        }
        m_l2_address = nullptr;
    };
    const L2_address *get_l2_address() const { return m_l2_address; };

    virtual neigh_val &operator=(const neigh_val &val)
    {
        if (this != &val) {
            m_l2_address = val.m_l2_address;
            m_trans_type = val.m_trans_type;
        }
        return *this;
    }

protected:
    friend class neigh_entry;
    friend class neigh_eth;
    transport_type_t m_trans_type;
    L2_address *m_l2_address;
};

class neigh_eth_val : public neigh_val {
public:
    neigh_eth_val()
    {
        m_trans_type = XLIO_TRANSPORT_ETH;
        zero_all_members();
    }

    neigh_val &operator=(const neigh_val &val) { return neigh_val::operator=(val); }

private:
    friend class neigh_eth;
};

/* neigh_entry inherits from cache_entry_subject where
 * Key = address (peer IP)
 * Val = class neigh_val
 */
typedef std::deque<neigh_send_data *> unsent_queue_t;

class neigh_entry : public cache_entry_subject<neigh_key, neigh_val *>,
                    public event_handler_rdma_cm,
                    public timer_handler {
public:
    enum type { UNKNOWN, MC, UC };

    enum state_t {
        ST_NOT_ACTIVE = 0,
        ST_INIT = 1,
        ST_INIT_RESOLUTION,
        ST_SOLICIT_SEND,
        ST_ADDR_RESOLVED,
        ST_ARP_RESOLVED,
        ST_PATH_RESOLVED,
        ST_READY,
        ST_ERROR,
        ST_LAST
    };

    enum event_t {
        EV_KICK_START = 0,
        EV_START_RESOLUTION,
        EV_ARP_RESOLVED,
        EV_ADDR_RESOLVED,
        EV_PATH_RESOLVED,
        EV_RDMA_RESOLVE_FAILED,
        EV_ERROR,
        EV_TIMEOUT_EXPIRED,
        EV_UNHANDLED,
        EV_LAST
    };

    friend class neighbour_table_mgr;

    neigh_entry(neigh_key key, transport_type_t type, bool is_init_resources = true);
    ~neigh_entry() override;

    // Overwrite cach_entry virtual function
    bool is_deletable() override;
    void clean_obj() override;

    // Implementation of pure virtual function: Don't use get_val function, instead use
    // get_peer_info
    bool get_val(INOUT neigh_val *&val) override
    {
        NOT_IN_USE(val);
        return false;
    };

    virtual bool get_peer_info(neigh_val *val);
    // Overriding subject's register_observer
    bool register_observer(const observer *const new_observer) override;
    // Overriding tostr to_str()
    const std::string to_str() const override;

    const char *event_to_str(event_t event) const;
    const char *state_to_str(state_t state) const;

    void handle_event_rdma_cm_cb(struct rdma_cm_event *p_event) override;
    void handle_neigh_event(neigh_nl_event *nl_ev);

    static void general_st_entry(const sm_info_t &func_info);
    static void general_st_leave(const sm_info_t &func_info);
    static void print_event_info(int state, int event, void *app_data);
    static void dofunc_enter_init(const sm_info_t &func_info);
    static void dofunc_enter_init_resolution(const sm_info_t &func_info);
    static void dofunc_enter_solicit_send(const sm_info_t &func_info);
    static void dofunc_enter_addr_resolved(const sm_info_t &func_info);
    static void dofunc_enter_error(const sm_info_t &func_info);
    static void dofunc_enter_not_active(const sm_info_t &func_info);
    static void dofunc_enter_ready(const sm_info_t &func_info);

    // Implementing pure virtual function of sender
    virtual int send(neigh_send_data &s_info);

protected:
    rdma_cm_id *m_cma_id;
    ip_address m_src_addr;
    enum rdma_port_space m_rdma_port_space;
    state_machine *m_state_machine;
    type m_type; // UC  / MC
    transport_type_t m_trans_type;
    bool m_state;
    unsent_queue_t m_unsent_queue;
    // Counter to sign that KickStart was already generated in ERROR_ST
    uint32_t m_err_counter;

    void *m_timer_handle;
    // members for sending arp
    uint32_t m_arp_counter;
    net_device_val *m_p_dev;
    ring *m_p_ring;
    xlio_ibv_send_wr m_send_wqe;
    ibv_sge m_sge;
    bool m_is_loopback;

    const std::string m_to_str;
    ring_user_id_t m_id;

    const ip_addr &get_dst_addr() const { return get_key().get_ip_addr(); }
    sa_family_t get_family() const { return get_dst_addr().get_family(); }

    virtual void priv_general_st_entry(const sm_info_t &func_info);
    virtual void priv_general_st_leave(const sm_info_t &func_info);
    virtual void priv_print_event_info(state_t state, event_t event);
    virtual void priv_kick_start_sm();
    virtual void priv_enter_not_active();
    virtual void priv_enter_error();
    virtual int priv_enter_init();
    virtual int priv_enter_init_resolution();
    virtual int priv_enter_solicit_send();
    virtual int priv_enter_addr_resolved();
    virtual int priv_enter_ready();

    bool priv_get_neigh_state(int &state);
    bool priv_get_neigh_l2(address_t &l2_addr);
    bool priv_is_reachable(int state) { return state & (NUD_REACHABLE | NUD_PERMANENT); }
    bool priv_is_failed(int state) { return state & (NUD_FAILED | NUD_INCOMPLETE); }

    void event_handler(event_t event, void *p_event_info = nullptr);
    void priv_event_handler_no_locks(event_t event, void *p_event_info = nullptr);

    virtual bool priv_handle_neigh_is_l2_changed(address_t) { return false; };
    void priv_handle_neigh_reachable_event();
    void priv_destroy_cma_id();
    virtual void *priv_register_timer_event(int timeout_msec, timer_handler *handler,
                                            timer_req_type_t req_type, void *user_data);
    void priv_unregister_timer();

    void send_discovery_request();
    virtual bool send_arp_request(bool) { return true; };
    virtual bool send_neighbor_solicitation() { return true; };
    virtual bool prepare_to_send_packet(neigh_send_data *) { return true; };
    void handle_timer_expired(void *user_data) override;

    virtual ring_user_id_t generate_ring_user_id(header *h = nullptr)
    {
        NOT_IN_USE(h);
        return m_p_ring->generate_id();
    };

    lock_mutex_recursive m_sm_lock;

private:
    bool m_is_first_send_arp;
    int m_ch_fd;
    const uint32_t m_n_sysvar_neigh_wait_till_send_arp_msec;
    const uint32_t m_n_sysvar_neigh_uc_arp_quata;
    const uint32_t m_n_sysvar_neigh_num_err_retries;
    ring_allocation_logic_tx m_ring_allocation_logic;
    event_t rdma_event_mapping(struct rdma_cm_event *p_event);
    void empty_unsent_queue();
    bool post_send_packet(neigh_send_data *n_send_data);
    bool post_send_udp_ipv4(neigh_send_data *n_send_data);
    bool post_send_udp_ipv6_not_fragmented(neigh_send_data *n_send_data);
    bool post_send_udp_ipv6_fragmented(neigh_send_data *n_send_data, size_t sz_udp_payload,
                                       size_t max_ip_payload_size);
    bool post_send_tcp(neigh_send_data *n_send_data);
};

class neigh_eth : public neigh_entry {
public:
    friend class neighbour_table_mgr;
    neigh_eth(neigh_key key);
    ~neigh_eth();
    bool get_peer_info(neigh_val *val) override;
    // Overriding neigh_entry register_observer
    bool register_observer(const observer *const new_observer) override;
    // Overriding neigh_entry is_deletable
    bool is_deletable() override;

protected:
    ring_user_id_t generate_ring_user_id(header *h = nullptr) override;

private:
    int build_mc_neigh_val();
    int build_uc_neigh_val();
    // Overriding neigh_entry priv_enter_ready
    int priv_enter_ready() override;
    int priv_enter_init() override;
    int priv_enter_init_resolution() override;
    bool priv_handle_neigh_is_l2_changed(address_t) override;
    bool send_arp_request(bool is_broadcast) override;
    bool send_neighbor_solicitation() override;
    bool prepare_to_send_packet(neigh_send_data *) override;
};

#endif /* NEIGHBOUR_H */
