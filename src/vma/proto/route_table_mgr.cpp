/*
 * Copyright (c) 2001-2022 Mellanox Technologies, Ltd. All rights reserved.
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

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <linux/rtnetlink.h>
#include <linux/netlink.h>
#include <netinet/in.h>
#include <netinet/ether.h>
#include <arpa/inet.h>

#include "utils/bullseye.h"
#include "utils/lock_wrapper.h"
#include "vlogger/vlogger.h"
#include "vma/util/vtypes.h"
#include "vma/util/utils.h"
#include "vma/sock/socket_fd_api.h"
#include "vma/sock/sock-redirect.h"
#include "vma/dev/net_device_table_mgr.h"
#include "vma/util/ip_address.h"
#include "route_table_mgr.h"
#include "rule_table_mgr.h"

// debugging macros
#define MODULE_NAME        "rtm:"
#define rt_mgr_if_logpanic __log_panic
#define rt_mgr_logerr      __log_err
#define rt_mgr_logwarn     __log_warn
#define rt_mgr_loginfo     __log_info
#define rt_mgr_logdbg      __log_dbg
#define rt_mgr_logfunc     __log_func
#define rt_mgr_logfuncall  __log_funcall

#define DEFAULT_ROUTE_TABLE_SIZE 256

route_table_mgr *g_p_route_table_mgr = NULL;

route_table_mgr::route_table_mgr()
    : netlink_socket_mgr()
    , cache_table_mgr<route_rule_table_key, route_val *>("route_table_mgr")
{
    rt_mgr_logdbg("");

    m_table_in4.reserve(DEFAULT_ROUTE_TABLE_SIZE);
    m_table_in6.reserve(DEFAULT_ROUTE_TABLE_SIZE);

    // Read Route table from kernel and save it in local variable.
    update_tbl();

    update_rte_netdev(m_table_in4);
    update_rte_netdev(m_table_in6);

    // Print table
    print_tbl();

    // register to netlink event
    g_p_netlink_handler->register_event(nlgrpROUTE, this);
    rt_mgr_logdbg("Registered to g_p_netlink_handler");

    rt_mgr_logdbg("Done");
}

route_table_mgr::~route_table_mgr()
{
    rt_mgr_logdbg("");

    // clear all route_entrys created in the constructor
    in_addr_route_entry_map_t::iterator iter;

    while ((iter = m_rte_list_for_each_net_dev.begin()) != m_rte_list_for_each_net_dev.end()) {
        delete (iter->second);
        m_rte_list_for_each_net_dev.erase(iter);
    }

    auto cache_itr = m_cache_tbl.begin();
    for (; cache_itr != m_cache_tbl.end(); cache_itr = m_cache_tbl.begin()) {
        delete (cache_itr->second);
        m_cache_tbl.erase(cache_itr);
    }
    rt_mgr_logdbg("Done");
}

void route_table_mgr::update_tbl()
{
    auto_unlocker lock(m_lock);

    netlink_socket_mgr::update_tbl(ROUTE_DATA_TYPE);

    rt_mgr_update_source_ip(m_table_in4);
    rt_mgr_update_source_ip(m_table_in6);

    return;
}

void route_table_mgr::rt_mgr_update_source_ip(route_table_t &table)
{
    // for route entries which still have no src ip and no gw
    for (auto iter = table.begin(); iter != table.end(); ++iter) {
        route_val &val = *iter;
        if (!val.get_src_addr().is_anyaddr() || !val.get_gw_addr().is_anyaddr()) {
            continue;
        }
        if (g_p_net_device_table_mgr) { // try to get src ip from net_dev list of the interface
            int longest_prefix = -1;
            ip_address correct_src;
            local_ip_list_t lip_list = g_p_net_device_table_mgr->get_ip_list(val.get_if_index());
            if (!lip_list.empty()) {
                for (auto lip_iter = lip_list.begin(); lip_list.end() != lip_iter; ++lip_iter) {
                    const ip_data_t &ip = *lip_iter;
                    if (val.get_family() == ip.local_addr.get_family() &&
                        val.get_dst_addr().is_equal_with_prefix(ip.local_addr, ip.prefixlen, val.get_family())) {
                        // found a match in routing table
                        if (ip.prefixlen > longest_prefix) {
                            longest_prefix = ip.prefixlen; // this is the longest prefix match
                            correct_src = ip.local_addr;
                        }
                    }
                }
                if (longest_prefix > -1) {
                    val.set_src_addr(correct_src);
                    continue;
                }
            }
        }
        // if still no src ip, get it from ioctl
        ip_addr src_addr {0};
        const char *if_name = val.get_if_name();
        if (!get_ip_addr_from_ifname(if_name, src_addr, val.get_family())) {
            assert(src_addr.get_family() == val.get_family());
            val.set_src_addr(src_addr);
        } else {
            // Failed mapping if_name to IP address
            rt_mgr_logwarn("could not figure out source ip for rtv = %s", val.to_str().c_str());
        }
    }

    // for route entries with gateway, do recursive search for src ip
    int num_unresolved_src = table.size();
    int prev_num_unresolved_src = 0;
    do {
        prev_num_unresolved_src = num_unresolved_src;
        num_unresolved_src = 0;
        for (auto iter = table.begin(); iter != table.end(); ++iter) {
            route_val &val = *iter;
            if (!val.get_gw_addr().is_anyaddr() && val.get_src_addr().is_anyaddr()) {
                route_val *p_val_dst;
                uint32_t table_id = val.get_table_id();
                if (find_route_val(table, val.get_gw_addr(), table_id, p_val_dst)) {
                    if (!p_val_dst->get_src_addr().is_anyaddr()) {
                        val.set_src_addr(p_val_dst->get_src_addr());
                    } else if (&val == p_val_dst) { // gateway of the entry lead to same entry
                        local_ip_list_t lip_offloaded_list =
                            g_p_net_device_table_mgr->get_ip_list(val.get_if_index());
                        for (auto lip_iter = lip_offloaded_list.begin();
                             lip_offloaded_list.end() != lip_iter; ++lip_iter) {
                            const ip_data_t &ip = *lip_iter;
                            if (ip_addr(val.get_gw_addr(), val.get_family()) == ip.local_addr) {
                                val.set_gw(ip_address::any_addr());
                                val.set_src_addr(ip.local_addr);
                                break;
                            }
                        }
                    }
                    // gateway and source are equal, no need of gw.
                    if (val.get_src_addr() == val.get_gw_addr()) {
                        val.set_gw(ip_address::any_addr());
                    }
                }
                if (val.get_src_addr().is_anyaddr()) {
                    num_unresolved_src++;
                }
            }
        }
    } while (num_unresolved_src && prev_num_unresolved_src > num_unresolved_src);

    // for route entries which still have no src ip
    for (auto iter = table.begin(); iter != table.end(); ++iter) {
        route_val &val = *iter;
        if (!val.get_src_addr().is_anyaddr()) {
            continue;
        }
        if (!val.get_gw_addr().is_anyaddr()) {
            rt_mgr_logdbg("could not figure out source ip for gw address. rtv = %s", val.to_str().c_str());
        }
        // if still no src ip, get it from ioctl
        ip_addr src_addr {0};
        const char *if_name = val.get_if_name();
        if (!get_ip_addr_from_ifname(if_name, src_addr, val.get_family())) {
            assert(src_addr.get_family() == val.get_family());
            val.set_src_addr(src_addr);
        } else {
            // Failed mapping if_name to IP address
            rt_mgr_logdbg("could not figure out source ip for rtv = %s", val.to_str().c_str());
        }
    }
}

void route_table_mgr::parse_entry(struct nlmsghdr *nl_header)
{
    int len;
    struct rtmsg *rt_msg;
    struct rtattr *rt_attribute;
    route_val val;

    // get route entry header
    rt_msg = (struct rtmsg *)NLMSG_DATA(nl_header);

    // we are not concerned about the local and default route table
    if (rt_msg->rtm_table == RT_TABLE_LOCAL) {
        return;
    }
    if (rt_msg->rtm_family != AF_INET && rt_msg->rtm_family != AF_INET6) {
        return;
    }

    val.set_family(rt_msg->rtm_family);
    val.set_protocol(rt_msg->rtm_protocol);
    val.set_scope(rt_msg->rtm_scope);
    val.set_type(rt_msg->rtm_type);
    val.set_table_id(rt_msg->rtm_table);
    val.set_dst_pref_len(rt_msg->rtm_dst_len);

    len = RTM_PAYLOAD(nl_header);
    rt_attribute = (struct rtattr *)RTM_RTA(rt_msg);

    for (; RTA_OK(rt_attribute, len); rt_attribute = RTA_NEXT(rt_attribute, len)) {
        parse_attr(rt_attribute, val);
    }
    val.set_state(true);

    route_table_t &table = val.get_family() == AF_INET ? m_table_in4 : m_table_in6;
    table.push_back(val);
}

void route_table_mgr::parse_attr(struct rtattr *rt_attribute, route_val &val)
{
    switch (rt_attribute->rta_type) {
    case RTA_DST:
        val.set_dst_addr(ip_address((void *)RTA_DATA(rt_attribute), val.get_family()));
        break;
    // next hop IPv4 address
    case RTA_GATEWAY:
        val.set_gw(ip_address((void *)RTA_DATA(rt_attribute), val.get_family()));
        break;
    // unique ID associated with the network interface
    case RTA_OIF:
        val.set_if_index(*(int *)RTA_DATA(rt_attribute));
        char if_name[IFNAMSIZ];
        if_indextoname(val.get_if_index(), if_name);
        val.set_if_name(if_name);
        break;
    case RTA_SRC:
    case RTA_PREFSRC:
        val.set_src_addr(ip_address((void *)RTA_DATA(rt_attribute), val.get_family()));
        break;
    case RTA_TABLE:
        val.set_table_id(*(uint32_t *)RTA_DATA(rt_attribute));
        break;
    case RTA_METRICS: {
        struct rtattr *rta = (struct rtattr *)RTA_DATA(rt_attribute);
        int len = RTA_PAYLOAD(rt_attribute);
        uint16_t type;
        while (RTA_OK(rta, len)) {
            type = rta->rta_type;
            switch (type) {
            case RTAX_MTU:
                val.set_mtu(*(uint32_t *)RTA_DATA(rta));
                break;
            default:
                rt_mgr_logdbg("got unexpected METRICS %d %x", type, *(uint32_t *)RTA_DATA(rta));
                break;
            }
            rta = RTA_NEXT(rta, len);
        }
        break;
    }
    default:
        rt_mgr_logdbg("got unexpected type %d %x", rt_attribute->rta_type,
                      *(uint32_t *)RTA_DATA(rt_attribute));
        break;
    }
}

void route_table_mgr::print_tbl()
{
    if (g_vlogger_level >= VLOG_DEBUG) {
        for (auto iter = m_table_in6.begin(); iter != m_table_in6.end(); ++iter) {
            (*iter).print_val();
        }
        for (auto iter = m_table_in4.begin(); iter != m_table_in4.end(); ++iter) {
            (*iter).print_val();
        }
    }
}

bool route_table_mgr::find_route_val(route_table_t &table, const ip_address &dst,
    uint32_t table_id, route_val *&p_val)
{
    rt_mgr_logfunc("dst addr '%s'", dst.to_str().c_str());

    route_val *correct_route_val = NULL;
    int longest_prefix = -1;

    for (auto iter = table.begin(); iter != table.end(); ++iter) {
        route_val &val = *iter;
        if (!val.is_deleted() && val.is_if_up()) { // Value was not deleted
            if (val.get_table_id() == table_id) { // Found a match in routing table ID
                if (val.get_dst_addr().is_equal_with_prefix(dst, val.get_dst_pref_len(), val.get_family())) {
                    // Found a match in routing table
                    if (val.get_dst_pref_len() > longest_prefix) {
                        // This is the longest prefix match
                        longest_prefix = val.get_dst_pref_len();
                        correct_route_val = &val;
                    }
                }
            }
        }
    }
    if (correct_route_val) {
        p_val = correct_route_val;
        rt_mgr_logdbg("found route val[%p]: %s", p_val, p_val->to_str().c_str());
        return true;
    }

    rt_mgr_logdbg("destination gw wasn't found");
    return false;
}

bool route_table_mgr::route_resolve(IN route_rule_table_key key, OUT route_result &res)
{
    const ip_address &dst_addr = key.get_dst_ip();
    rt_mgr_logdbg("dst addr '%s'", dst_addr.to_str().c_str());

    route_table_t &rt = key.get_family() == AF_INET ? m_table_in4 : m_table_in6;
    route_val *p_val = NULL;
    std::deque<uint32_t> table_id_list;

    g_p_rule_table_mgr->rule_resolve(key, table_id_list);

    auto_unlocker lock(m_lock);
    for (auto iter = table_id_list.begin(); iter != table_id_list.end(); ++iter) {
        if (find_route_val(rt, dst_addr, *iter, p_val)) {
            res.p_src = p_val->get_src_addr().get_in_addr();
            rt_mgr_logdbg("dst ip '%s' resolved to src addr '%d.%d.%d.%d'",
                          dst_addr.to_str().c_str(), NIPQUAD(res.p_src));
            res.p_gw = p_val->get_gw_addr().get_in_addr();
            rt_mgr_logdbg("dst ip '%s' resolved to gw addr '%d.%d.%d.%d'",
                          dst_addr.to_str().c_str(), NIPQUAD(res.p_gw));
            res.mtu = p_val->get_mtu();
            rt_mgr_logdbg("found route mtu %d", res.mtu);
            return true;
        }
    }
    /* prevent usage on false return */
    return false;
}

void route_table_mgr::update_rte_netdev(route_table_t &table)
{
    // Create route_entry for each netdev to receive port up/down events for net_dev_entry
    for (auto iter = table.begin(); iter != table.end(); ++iter) {
        route_val &val = *iter;
        const ip_address &src_addr = val.get_src_addr();
        auto iter_rte = m_rte_list_for_each_net_dev.find(src_addr);
        // If src_addr of interface exists in the map, no need to create another route_entry
        if (iter_rte == m_rte_list_for_each_net_dev.end()) {
            const ip_address &dst_ip = src_addr;
            const ip_address &src_ip = ip_address::any_addr();
            uint8_t tos = 0;
            m_rte_list_for_each_net_dev[src_addr] =
                create_new_entry(route_rule_table_key(dst_ip, src_ip, val.get_family(), tos), NULL);
        }
    }
}

void route_table_mgr::update_entry(INOUT route_entry *p_ent, bool b_register_to_net_dev /*= false*/)
{
    rt_mgr_logdbg("entry [%p]", p_ent);

    route_table_t &rt = p_ent->get_key().get_family() == AF_INET ? m_table_in4 : m_table_in6;

    auto_unlocker lock(m_lock);
    if (p_ent && !p_ent->is_valid()) { // if entry is found in the collection and is not valid
        rt_mgr_logdbg("route_entry is not valid-> update value");
        rule_entry *p_rr_entry = p_ent->get_rule_entry();
        std::deque<rule_val *> *p_rr_val;
        if (p_rr_entry && p_rr_entry->get_val(p_rr_val)) {
            route_val *p_val = NULL;
            const ip_address &peer_ip = p_ent->get_key().get_dst_ip();
            for (auto p_rule_val = p_rr_val->begin(); p_rule_val != p_rr_val->end(); ++p_rule_val) {
                uint32_t table_id = (*p_rule_val)->get_table_id();
                if (find_route_val(rt, peer_ip, table_id, p_val)) {
                    p_ent->set_val(p_val);
                    if (b_register_to_net_dev) {
                        // Check if broadcast IPv4 which is NOT supported
                        if ((p_ent->get_key().get_family() == AF_INET) && (peer_ip == ip_address::broadcast4_addr())) {
                            rt_mgr_logdbg("Disabling Offload for broadcast route_entry '%s'",
                                          p_ent->to_str().c_str());
                            // Need to route traffic to/from OS
                            // Prevent registering of net_device to route entry
                        } else {
                            // register to net device for bonding events
                            p_ent->register_to_net_device();
                        }
                    }
                    // All good, validate the new route entry
                    p_ent->set_entry_valid();
                    break;
                } else {
                    rt_mgr_logdbg("could not find route val for route_entry '%s in table %u'",
                                  p_ent->to_str().c_str(), table_id);
                }
            }
        } else {
            rt_mgr_logdbg("rule entry is not valid");
        }
    }
}

route_entry *route_table_mgr::create_new_entry(route_rule_table_key key, const observer *obs)
{
    // no need for lock - lock is activated in cache_collection_mgr::register_observer

    rt_mgr_logdbg("");
    NOT_IN_USE(obs);
    route_entry *p_ent = new route_entry(key);
    update_entry(p_ent, true);
    rt_mgr_logdbg("new entry %p created successfully", p_ent);
    return p_ent;
}

void route_table_mgr::new_route_event(route_val *netlink_route_val)
{
    if (!netlink_route_val) {
        rt_mgr_logdbg("Invalid route entry");
        return;
    }

    route_val val;

    val.set_dst_addr(netlink_route_val->get_dst_addr());
    val.set_dst_pref_len(netlink_route_val->get_dst_pref_len());
    val.set_src_addr(netlink_route_val->get_src_addr());
    val.set_gw(netlink_route_val->get_gw_addr());
    val.set_family(netlink_route_val->get_family());
    val.set_protocol(netlink_route_val->get_protocol());
    val.set_scope(netlink_route_val->get_scope());
    val.set_type(netlink_route_val->get_type());
    val.set_table_id(netlink_route_val->get_table_id());
    val.set_if_index(netlink_route_val->get_if_index());
    val.set_if_name(const_cast<char *>(netlink_route_val->get_if_name()));
    val.set_mtu((netlink_route_val->get_mtu()));
    val.set_state(true);
    val.print_val();

    auto_unlocker lock(m_lock);
    route_table_t &table = val.get_family() == AF_INET ? m_table_in4 : m_table_in6;
    table.push_back(val);
}

void route_table_mgr::notify_cb(event *ev)
{
    rt_mgr_logdbg("received route event from netlink");

    route_nl_event *route_netlink_ev = dynamic_cast<route_nl_event *>(ev);
    if (!route_netlink_ev) {
        rt_mgr_logwarn("Received non route event!!!");
        return;
    }

    netlink_route_info *p_netlink_route_info = route_netlink_ev->get_route_info();
    if (!p_netlink_route_info) {
        rt_mgr_logdbg("Received invalid route event!!!");
        return;
    }

    switch (route_netlink_ev->nl_type) {
    case RTM_NEWROUTE:
        new_route_event(p_netlink_route_info->get_route_val());
        break;
#if 0
		case RTM_DELROUTE:
			del_route_event(p_netlink_route_info->get_route_val());
			break;
#endif
    default:
        rt_mgr_logdbg("Route event (%u) is not handled", route_netlink_ev->nl_type);
        break;
    }
}
