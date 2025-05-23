/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#include <cassert>

#include "route_info.h"
#include "config.h"
#include "core/util/if.h"
#include "core/util/libxlio.h"
#include "vlogger/vlogger.h"

#define MODULE_NAME "route_info:"

netlink_route_info::netlink_route_info(struct rtnl_route *nl_route_obj)
    : m_route_val()
{
    fill(nl_route_obj);
}

netlink_route_info::~netlink_route_info()
{
}

void netlink_route_info::fill(struct rtnl_route *nl_route_obj)
{
    if (!nl_route_obj) {
        return;
    }

    int table = rtnl_route_get_table(nl_route_obj);
    if (table > 0) {
        m_route_val.set_table_id(table);
    }

    int scope = rtnl_route_get_scope(nl_route_obj);
    if (scope > 0) {
        m_route_val.set_scope(scope);
    }

    uint32_t mtu = 0;
    int rc = rtnl_route_get_metric(nl_route_obj, RTAX_MTU, &mtu);
    if (rc == 0) {
        m_route_val.set_mtu(mtu);
    } else {
        __log_dbg("Failed to parse route metric MTU error=%d", rc);
    }

    int protocol = rtnl_route_get_protocol(nl_route_obj);
    if (protocol > 0) {
        m_route_val.set_protocol(protocol);
    }

    int family = rtnl_route_get_family(nl_route_obj);
    if (family > 0) {
        m_route_val.set_family(family);
    }

    int type = rtnl_route_get_type(nl_route_obj);
    if (type > 0) {
        m_route_val.set_type(type);
    }

    struct nl_addr *addr = rtnl_route_get_dst(nl_route_obj);
    if (addr) {
        // TODO: improve error handling
        assert(family == nl_addr_get_family(addr));
        unsigned int dst_prefixlen = nl_addr_get_prefixlen(addr);
        m_route_val.set_dst_pref_len(dst_prefixlen);
        m_route_val.set_dst_addr(ip_address((void *)nl_addr_get_binary_addr(addr), family));
    }

    addr = rtnl_route_get_pref_src(nl_route_obj);
    if (addr) {
        // TODO: improve error handling
        assert(family == nl_addr_get_family(addr));
        m_route_val.set_src_addr(ip_address((void *)nl_addr_get_binary_addr(addr), family));
    }

    rtnl_nexthop *nh = rtnl_route_nexthop_n(nl_route_obj, 0);
    if (nh) {
        int oif = rtnl_route_nh_get_ifindex(nh);
        if (oif > 0) {
            m_route_val.set_if_index(oif);
            char if_name[IFNAMSIZ];
            if_indextoname(oif, if_name);
            m_route_val.set_if_name(if_name);
        }

        addr = rtnl_route_nh_get_gateway(nh);
        if (addr) {
            // TODO: improve error handling
            assert(family == nl_addr_get_family(addr));
            m_route_val.set_gw(ip_address((void *)nl_addr_get_binary_addr(addr), family));
        }
    }
}
