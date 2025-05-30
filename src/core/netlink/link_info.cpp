/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#include "link_info.h"
#include "vlogger/vlogger.h"

#define MODULE_NAME "netlink_event"

#define ADDR_MAX_STR_LEN (128)

netlink_link_info::netlink_link_info(struct rtnl_link *link)
    : /*arptype(0),*/ broadcast_str("")
    , flags(0)
    , ifindex(0)
    , /*mode(0),*/ master_ifindex(0)
    , mtu(0)
    , name("")
    , addr_family(0)
    , operstate(0)
    , txqlen(0)
{
    fill(link);
}

void netlink_link_info::fill(struct rtnl_link *link)
{
    if (link) {
        // arptype=rtnl_link_get_arptype(link);
        addr_family = rtnl_link_get_family(link);
        flags = rtnl_link_get_flags(link);
        ifindex = rtnl_link_get_ifindex(link);
        master_ifindex = rtnl_link_get_master(link);
        mtu = rtnl_link_get_mtu(link);
        txqlen = rtnl_link_get_txqlen(link);
        operstate = rtnl_link_get_operstate(link);
        // mode=rtnl_link_get_linkmode(link);

        nl_addr *addr;
        char addr_str[ADDR_MAX_STR_LEN + 1];

        const char *namestr = rtnl_link_get_name(link);
        if (namestr) {
            name = namestr;
        }

        addr = rtnl_link_get_broadcast(link);
        if (addr) {
            broadcast_str = nl_addr2str(addr, addr_str, ADDR_MAX_STR_LEN);
        }
    }
}

const std::string netlink_link_info::get_operstate2str() const
{
    char operstate_str[256];
    return rtnl_link_operstate2str(operstate, operstate_str, 255);
}
