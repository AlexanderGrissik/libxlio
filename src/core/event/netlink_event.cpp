/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#include "netlink_event.h"
#include "vlogger/vlogger.h"

#include <netlink/route/neighbour.h>
#include <netlink/route/link.h>
#include <stdio.h>

#define TOSTR_MAX_SIZE 4096

netlink_event::netlink_event(struct nlmsghdr *hdr, void *notifier)
    : event(notifier)
    , nl_type(0)
    , nl_pid(0)
    , nl_seq(0)
{
    if (hdr) {
        nl_type = hdr->nlmsg_type;
        nl_pid = hdr->nlmsg_pid;
        nl_seq = hdr->nlmsg_seq;
    }
}

const std::string netlink_event::to_str() const
{
    char outstr[TOSTR_MAX_SIZE];
    sprintf(outstr, "%s. NETLINK: TYPE=%u, PID=%u SEQ=%u", event::to_str().c_str(), nl_type, nl_pid,
            nl_seq);
    return std::string(outstr);
}

const std::string neigh_nl_event::to_str() const
{
    char outstr[TOSTR_MAX_SIZE];
    sprintf(outstr,
            "%s. NEIGH: DST_ADDR=%s LINK_ADDR=%s FLAGS=%u IFINDEX=%d STATE=%d TYPE=%d FAMILY=%d",
            netlink_event::to_str().c_str(), m_neigh_info->dst_addr_str.c_str(),
            m_neigh_info->lladdr_str.c_str(), m_neigh_info->flags, m_neigh_info->ifindex,
            m_neigh_info->state, m_neigh_info->type, m_neigh_info->addr_family);
    return std::string(outstr);
}

const std::string route_nl_event::to_str() const
{
    char outstr[TOSTR_MAX_SIZE];
    const route_val &p_route_val = m_route_info->get_route_val();

    sprintf(outstr,
            "%s. ROUTE: TABLE=%u SCOPE=%u FAMILY=%u PROTOCOL=%u DST_ADDR=%s DST_PREFIX=%u "
            "TYPE=%u PREF_SRC=%s IFF_NAME=%s",
            netlink_event::to_str().c_str(), p_route_val.get_table_id(), p_route_val.get_scope(),
            p_route_val.get_family(), p_route_val.get_protocol(),
            p_route_val.get_dst_addr().to_str(p_route_val.get_family()).c_str(),
            p_route_val.get_dst_pref_len(), p_route_val.get_type(),
            p_route_val.get_src_addr().to_str(p_route_val.get_family()).c_str(),
            p_route_val.get_if_name());

    return std::string(outstr);
}

neigh_nl_event::neigh_nl_event(struct nlmsghdr *hdr, struct rtnl_neigh *neigh, void *notifier)
    : netlink_event(hdr, notifier)
    , m_neigh_info(nullptr)
{
    m_neigh_info = new netlink_neigh_info(neigh);
    if ((!hdr) && (neigh)) {
        nl_type = rtnl_neigh_get_type(neigh);
    }
}

neigh_nl_event::~neigh_nl_event()
{
    if (m_neigh_info) {
        delete m_neigh_info;
    }
}

route_nl_event::route_nl_event(struct nlmsghdr *hdr, struct rtnl_route *route, void *notifier)
    : netlink_event(hdr, notifier)
    , m_route_info(nullptr)
{
    m_route_info = new netlink_route_info(route);
}

route_nl_event::~route_nl_event()
{
    if (m_route_info) {
        delete m_route_info;
    }
}
link_nl_event::link_nl_event(struct nlmsghdr *hdr, struct rtnl_link *rt_link, void *notifier)
    : netlink_event(hdr, notifier)
{
    m_link_info = new netlink_link_info(rt_link);
}

link_nl_event::~link_nl_event()
{
    if (m_link_info) {
        delete m_link_info;
    }
}

const std::string link_nl_event::to_str() const
{
    char outstr[TOSTR_MAX_SIZE];
    sprintf(outstr,
            //"%s. LINK: ARPTYPE=%u BROADCAST=%s ADDR_FAMILY=%d FLAGS=%u IFINDEX=%d MODE=%u
            // MASTER_IFINDEX=%d MTU=%u NAME=%s OPERSTATE=%u TXQLEN=%u",
            "%s. LINK: BROADCAST=%s ADDR_FAMILY=%d FLAGS=%u IFINDEX=%d MASTER_IFINDEX=%d MTU=%u "
            "NAME=%s OPERSTATE=%s TXQLEN=%u",
            netlink_event::to_str().c_str(), /* m_link_info->arptype,*/
            m_link_info->broadcast_str.c_str(), m_link_info->addr_family, m_link_info->flags,
            m_link_info->ifindex,
            /*m_link_info->mode,*/ m_link_info->master_ifindex, m_link_info->mtu,
            m_link_info->name.c_str(), m_link_info->get_operstate2str().c_str(),
            m_link_info->txqlen);

    return std::string(outstr);
}
