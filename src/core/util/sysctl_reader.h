/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#ifndef SYSCNTL_READER_H_
#define SYSCNTL_READER_H_

#include "vlogger/vlogger.h"
#include "utils.h"

struct sysctl_tcp_mem {
    int min_value;
    int default_value;
    int max_value;
};

struct tcp_keepalive_info {
    int idle_secs;
    int interval_secs;
    int num_probes;
};

class sysctl_reader_t {

private:
    int sysctl_read(const char *path, int argument_num, const char *format, ...)
    {

        FILE *pfile = fopen(path, "r");
        int ans;

        if (!pfile) {
            return -1;
        }

        va_list arg;
        va_start(arg, format);
        ans = vfscanf(pfile, format, arg);
        va_end(arg);

        fclose(pfile);

        if (ans != argument_num) {
            return -1;
        }

        return 0;
    }

    void init() {}

    sysctl_reader_t()
    {
        this->init();
        this->update_all();
    }

public:
    static sysctl_reader_t &instance()
    {
        static sysctl_reader_t the_instance;
        return the_instance;
    }

    void update_all()
    {
        get_tcp_max_syn_backlog(true);
        get_listen_maxconn(true);
        get_tcp_wmem(true);
        get_tcp_rmem(true);
        get_tcp_window_scaling(true);
        get_net_core_rmem_max(true);
        get_net_core_wmem_max(true);
        get_net_ipv4_tcp_timestamps(true);
        get_net_ipv4_ttl(true);
        get_igmp_max_membership(true);
        get_igmp_max_source_membership(true);
        get_mld_max_source_membership(true);
        get_net_ipv6_hop_limit(true);
        get_ipv6_bindv6only(true);
        get_ipv6_conf_all_optimistic_dad(true);
        get_ipv6_conf_all_use_optimistic(true);
        get_tcp_keepalive_info(true);
    }

    int get_tcp_max_syn_backlog(bool update = false)
    {
        static int val;
        if (update) {
            val = read_file_to_int("/proc/sys/net/ipv4/tcp_max_syn_backlog", 1024);
        }
        return val;
    }

    int get_listen_maxconn(bool update = false)
    {
        static int val;
        if (update) {
            val = read_file_to_int("/proc/sys/net/core/somaxconn", SOMAXCONN);
        }
        return val;
    }

    const sysctl_tcp_mem *get_tcp_wmem(bool update = false)
    {
        static sysctl_tcp_mem tcp_mem;
        if (update) {
            if (sysctl_read("/proc/sys/net/ipv4/tcp_wmem", 3, "%d %d %d", &tcp_mem.min_value,
                            &tcp_mem.default_value, &tcp_mem.max_value) == -1) {
                tcp_mem.min_value = 4096;
                tcp_mem.default_value = 16384;
                tcp_mem.max_value = 4194304;
                vlog_printf(VLOG_WARNING,
                            "sysctl_reader failed to read net.ipv4.tcp_wmem values - Using "
                            "defaults : %d %d %d\n",
                            tcp_mem.min_value, tcp_mem.default_value, tcp_mem.max_value);
            }
        }
        return &tcp_mem;
    }

    const sysctl_tcp_mem *get_tcp_rmem(bool update = false)
    {
        static sysctl_tcp_mem tcp_mem;
        if (update) {
            if (sysctl_read("/proc/sys/net/ipv4/tcp_rmem", 3, "%d %d %d", &tcp_mem.min_value,
                            &tcp_mem.default_value, &tcp_mem.max_value) == -1) {
                // defaults were taken based on man (7) tcp
                tcp_mem.min_value = 4096;
                tcp_mem.default_value = 87380;
                tcp_mem.max_value = 4194304;
                vlog_printf(VLOG_WARNING,
                            "sysctl_reader failed to read net.ipv4.tcp_rmem values - Using "
                            "defaults : %d %d %d\n",
                            tcp_mem.min_value, tcp_mem.default_value, tcp_mem.max_value);
            }
        }
        return &tcp_mem;
    }

    const tcp_keepalive_info get_tcp_keepalive_info(bool update = false)
    {
        static tcp_keepalive_info val = {7200, 75, 9};
        auto read_file_to_positive_int = [](const char *path, int default_value) {
            int ret = read_file_to_int(path, default_value);
            return ret > 0 ? ret : default_value;
        };
        if (update) {
            val.idle_secs =
                read_file_to_positive_int("/proc/sys/net/ipv4/tcp_keepalive_time", val.idle_secs);
            val.interval_secs = read_file_to_positive_int("/proc/sys/net/ipv4/tcp_keepalive_intvl",
                                                          val.interval_secs);
            val.num_probes = read_file_to_positive_int("/proc/sys/net/ipv4/tcp_keepalive_probes",
                                                       val.num_probes);
        }
        return val;
    }

    int get_tcp_window_scaling(bool update = false)
    {
        static int val;
        if (update) {
            val = read_file_to_int("/proc/sys/net/ipv4/tcp_window_scaling", 0);
        }
        return val;
    }

    int get_net_core_rmem_max(bool update = false)
    {
        static int val;
        if (update) {
            val = read_file_to_int("/proc/sys/net/core/rmem_max", 229376);
        }
        return val;
    }

    int get_net_core_wmem_max(bool update = false)
    {
        static int val;
        if (update) {
            val = read_file_to_int("/proc/sys/net/core/wmem_max", 229376);
        }
        return val;
    }

    int get_net_ipv4_tcp_timestamps(bool update = false)
    {
        static int val;
        if (update) {
            val = read_file_to_int("/proc/sys/net/ipv4/tcp_timestamps", 0);
        }
        return val;
    }

    int get_net_ipv4_ttl(bool update = false)
    {
        static int val;
        if (update) {
            val = read_file_to_int("/proc/sys/net/ipv4/ip_default_ttl", 64);
        }
        return val;
    }

    int get_net_ipv6_hop_limit(bool update = false)
    {
        static int val;
        if (update) {
            val = read_file_to_int("/proc/sys/net/ipv6/conf/default/hop_limit", 64);
        }
        return val;
    }

    int get_igmp_max_membership(bool update = false)
    {
        static int val;
        if (update) {
            val = read_file_to_int("/proc/sys/net/ipv4/igmp_max_memberships", 1024);
            if (0 > val) {
                vlog_printf(VLOG_WARNING, "failed to read get_igmp_max_membership value\n");
            }
        }
        return val;
    }

    int get_igmp_max_source_membership(bool update = false)
    {
        static int val;
        if (update) {
            val = read_file_to_int("/proc/sys/net/ipv4/igmp_max_msf", 1024);
            if (0 > val) {
                vlog_printf(VLOG_WARNING, "failed to read get_igmp_max_source_membership value\n");
            }
        }
        return val;
    }

    int get_mld_max_source_membership(bool update = false)
    {
        static int val;
        if (update) {
            val = read_file_to_int("/proc/sys/net/ipv6/mld_max_msf", 64);
            if (0 > val) {
                vlog_printf(VLOG_WARNING, "failed to read get_mld_max_source_membership value\n");
            }
        }
        return val;
    }

    int get_ipv6_bindv6only(bool update = false)
    {
        static int val;
        if (update) {
            val = read_file_to_int("/proc/sys/net/ipv6/bindv6only", 0);
            if (0 > val) {
                vlog_printf(VLOG_WARNING, "failed to read bindv6only value\n");
            }
        }
        return val;
    }

    int get_ipv6_conf_all_optimistic_dad(bool update = false)
    {
        static int val;
        if (update) {
            val = read_file_to_int("/proc/sys/net/ipv6/conf/all/optimistic_dad", 0, VLOG_DEBUG);
            if (0 > val) {
                vlog_printf(VLOG_DEBUG, "failed to read ipv6/conf/all/optimistic_dad value\n");
            }
        }
        return val;
    }

    int get_ipv6_conf_all_use_optimistic(bool update = false)
    {
        static int val;
        if (update) {
            val = read_file_to_int("/proc/sys/net/ipv6/conf/all/use_optimistic", 0, VLOG_DEBUG);
            if (0 > val) {
                vlog_printf(VLOG_DEBUG, "failed to read ipv6/conf/all/use_optimistic value\n");
            }
        }
        return val;
    }

    int get_ipv6_if_optimistic_dad(const char *if_name)
    {
        if (!if_name) {
            vlog_printf(VLOG_DEBUG, "get_ipv6_if_optimistic_dad if_name is null\n");
            return 0;
        }

        std::string conf_name = "/proc/sys/net/ipv6/conf/";
        conf_name += if_name;
        conf_name += "/optimistic_dad";
        int val = read_file_to_int(conf_name.c_str(), 0, VLOG_DEBUG);
        if (0 > val) {
            vlog_printf(VLOG_DEBUG, "failed to read ipv6/conf/%s/optimistic_dad value\n", if_name);
        }
        return val;
    }

    int get_ipv6_if_use_optimistic(const char *if_name)
    {
        if (!if_name) {
            vlog_printf(VLOG_DEBUG, "get_ipv6_if_use_optimistic if_name is null\n");
            return 0;
        }

        std::string conf_name = "/proc/sys/net/ipv6/conf/";
        conf_name += if_name;
        conf_name += "/use_optimistic";
        int val = read_file_to_int(conf_name.c_str(), 0, VLOG_DEBUG);
        if (0 > val) {
            vlog_printf(VLOG_DEBUG, "failed to read ipv6/conf/%s/use_optimistic value\n", if_name);
        }
        return val;
    }

    int get_ipv6_if_use_tempaddr(const char *if_name)
    {
        if (!if_name) {
            vlog_printf(VLOG_DEBUG, "get_ipv6_if_use_tempaddr if_name is null\n");
            return 0;
        }

        std::string conf_name = "/proc/sys/net/ipv6/conf/";
        conf_name += if_name;
        conf_name += "/use_tempaddr";
        int val = read_file_to_int(conf_name.c_str(), 0, VLOG_DEBUG);
        if (0 > val) {
            vlog_printf(VLOG_DEBUG, "failed to read ipv6/conf/%s/use_tempaddr value\n", if_name);
        }
        return val;
    }
};

#endif /* SYSCNTL_READER_H_ */
