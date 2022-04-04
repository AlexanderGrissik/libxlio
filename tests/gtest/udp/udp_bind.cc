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

#include "common/def.h"
#include "common/log.h"
#include "common/sys.h"
#include "common/base.h"
#include "src/vma/util/sock_addr.h"
#include "udp_base.h"

class udp_bind : public udp_base {
public:
    udp_bind()
        : m_src_port(server_addr.addr.sin_family == AF_INET ? server_addr.addr.sin_port
                                                            : server_addr.addr6.sin6_port)
        , m_addr_all_ipv4(AF_INET, &ip_address::any_addr().get_in4_addr(), m_src_port)
        , m_addr_all_ipv6(AF_INET6, &ip_address::any_addr().get_in6_addr(), m_src_port)
    {
    }

protected:
    bool create_ipv4_ipv6_sockets(bool reuse_addr)
    {
        m_fd4 = udp_base::sock_create(AF_INET, reuse_addr);
        m_fd6 = udp_base::sock_create(AF_INET6, reuse_addr);
        EXPECT_LE(0, m_fd4);
        EXPECT_LE(0, m_fd6);
        return (m_fd4 > 0 && m_fd6 > 0);
    }

    bool recreate_ipv6_socket(bool reuse_addr)
    {
        int rc = close(m_fd6);
        EXPECT_EQ(0, rc);
        m_fd6 = udp_base::sock_create(AF_INET6, reuse_addr);
        EXPECT_LE(0, m_fd6);
        return (m_fd6 > 0);
    }

    bool close_ipv4_ipv6_sockets()
    {
        int rc4 = close(m_fd4);
        EXPECT_EQ(0, rc4);
        int rc6 = close(m_fd6);
        EXPECT_EQ(0, rc6);
        return (rc4 == 0 && rc6 == 0);
    }

    bool set_ipv6only(bool ipv6only)
    {
        int val = (ipv6only ? 1 : 0);
        int rc = setsockopt(m_fd6, IPPROTO_IPV6, IPV6_V6ONLY, &val, sizeof(val));
        EXPECT_EQ(0, rc);
        return (rc == 0);
    }

    int bind_all4()
    {
        return bind(m_fd4, m_addr_all_ipv4.get_p_sa(), m_addr_all_ipv4.get_socklen());
    }

    int bind_all6()
    {
        return bind(m_fd6, m_addr_all_ipv6.get_p_sa(), m_addr_all_ipv6.get_socklen());
    }

private:
    int m_fd4 = 0;
    int m_fd6 = 0;
    in_port_t m_src_port;
    sock_addr m_addr_all_ipv4;
    sock_addr m_addr_all_ipv6;
};

/**
 * @test udp_bind.ti_1
 * @brief
 *    bind(SOCK_DGRAM) socket to local ip
 * @details
 */
TEST_F(udp_bind, ti_1)
{
    int rc = EOK;
    int fd;

    fd = udp_base::sock_create();
    ASSERT_LE(0, fd);

    errno = EOK;
    rc = bind(fd, (struct sockaddr *)&client_addr, sizeof(client_addr));
    EXPECT_EQ(EOK, errno);
    EXPECT_EQ(0, rc);

    close(fd);
}

/**
 * @test udp_bind.ti_2
 * @brief
 *    bind(SOCK_DGRAM) socket to remote ip
 * @details
 */
TEST_F(udp_bind, ti_2)
{
    int rc = EOK;
    int fd;

    fd = udp_base::sock_create();
    ASSERT_LE(0, fd);

    errno = EOK;
    rc = bind(fd, (struct sockaddr *)&remote_addr, sizeof(remote_addr));
    EXPECT_EQ(EADDRNOTAVAIL, errno);
    EXPECT_GT(0, rc);

    close(fd);
}

/**
 * @test udp_bind.ti_3
 * @brief
 *    bind(SOCK_DGRAM) socket twice
 * @details
 */
TEST_F(udp_bind, ti_3)
{
    int rc = EOK;
    int fd;
    sockaddr_store_t addr1;
    sockaddr_store_t addr2;

    fd = udp_base::sock_create();
    ASSERT_LE(0, fd);

    memcpy(&addr1, &client_addr, sizeof(addr1));
    sys_set_port((struct sockaddr *)&addr1, 17001);

    errno = EOK;
    rc = bind(fd, (struct sockaddr *)&addr1, sizeof(addr1));
    EXPECT_EQ(EOK, errno);
    EXPECT_EQ(0, rc);

    memcpy(&addr2, &client_addr, sizeof(addr2));
    sys_set_port((struct sockaddr *)&addr2, 17002);

    errno = EOK;
    rc = bind(fd, (struct sockaddr *)&addr2, sizeof(addr2));
    EXPECT_EQ(EINVAL, errno);
    EXPECT_GT(0, rc);

    close(fd);
}

/**
 * @test udp_bind.ti_4
 * @brief
 *    bind(SOCK_DGRAM) two sockets on the same ip
 * @details
 */
TEST_F(udp_bind, ti_4)
{
    int rc = EOK;
    int fd;
    int fd2;
    sockaddr_store_t addr;

    fd = udp_base::sock_create();
    ASSERT_LE(0, fd);

    memcpy(&addr, &client_addr, sizeof(addr));
    sys_set_port((struct sockaddr *)&addr, 17001);

    errno = EOK;
    rc = bind(fd, (struct sockaddr *)&addr, sizeof(addr));
    EXPECT_EQ(EOK, errno);
    EXPECT_EQ(0, rc);

    fd2 = udp_base::sock_create();
    ASSERT_LE(0, fd);

    errno = EOK;
    rc = bind(fd2, (struct sockaddr *)&addr, sizeof(addr));
    EXPECT_EQ(EADDRINUSE, errno);
    EXPECT_GT(0, rc);

    close(fd);
    close(fd2);
}

/**
 * @test udp_bind.bind_IP4_6_dual_stack_no_reuse_addr
 * @brief
 *    Bind to the same port IPv4 then IPv6-Dual-socket.
 *    SO_REUSEADDR = false.
 * @details
 */
TEST_F(udp_bind, bind_IP4_6_dual_stack_no_reuse_addr)
{
    ASSERT_TRUE(create_ipv4_ipv6_sockets(false));
    ASSERT_TRUE(set_ipv6only(false));

    EXPECT_EQ(0, bind_all4());
    EXPECT_NE(0, bind_all6());
    EXPECT_EQ(EADDRINUSE, errno);
    ASSERT_TRUE(set_ipv6only(true));
    EXPECT_EQ(0, bind_all6());

    EXPECT_TRUE(close_ipv4_ipv6_sockets());
}

/**
 * @test udp_bind.bind_IP6_4_dual_stack_no_reuse_addr
 * @brief
 *    Bind to the same port IPv6-Dual-socket then IPv4.
 *    SO_REUSEADDR = false.
 * @details
 */
TEST_F(udp_bind, bind_IP6_4_dual_stack_no_reuse_addr)
{
    ASSERT_TRUE(create_ipv4_ipv6_sockets(false));
    ASSERT_TRUE(set_ipv6only(false));

    EXPECT_EQ(0, bind_all6());
    EXPECT_NE(0, bind_all4());
    EXPECT_EQ(EADDRINUSE, errno);
    ASSERT_TRUE(recreate_ipv6_socket(false));
    ASSERT_TRUE(set_ipv6only(true));
    EXPECT_EQ(0, bind_all6());
    EXPECT_EQ(0, bind_all4());

    EXPECT_TRUE(close_ipv4_ipv6_sockets());
}

/**
 * @test udp_bind.bind_IP4_6_dual_stack_reuse_addr
 * @brief
 *    Bind to the same port IPv4 then IPv6-Dual-socket.
 *    SO_REUSEADDR = true.
 * @details
 */
TEST_F(udp_bind, bind_IP4_6_dual_stack_reuse_addr)
{
    ASSERT_TRUE(create_ipv4_ipv6_sockets(true));
    ASSERT_TRUE(set_ipv6only(false));

    EXPECT_EQ(0, bind_all4());
    EXPECT_EQ(0, bind_all6());

    EXPECT_TRUE(close_ipv4_ipv6_sockets());
}

/**
 * @test tcp_bind.bind_IP6_4_dual_stack_reuse_addr
 * @brief
 *    Bind to the same port IPv6-Dual-socket then IPv4.
 *    SO_REUSEADDR = true.
 * @details
 */
TEST_F(udp_bind, bind_IP6_4_dual_stack_reuse_addr)
{
    ASSERT_TRUE(create_ipv4_ipv6_sockets(true));
    ASSERT_TRUE(set_ipv6only(false));

    EXPECT_EQ(0, bind_all6());
    EXPECT_EQ(0, bind_all4());

    EXPECT_TRUE(close_ipv4_ipv6_sockets());
}
