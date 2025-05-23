/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#include "common/def.h"
#include "common/log.h"
#include "common/sys.h"
#include "common/base.h"
#include "common/cmn.h"
#include "udp_base.h"

class udp_sendto : public udp_base {};

/**
 * @test udp_sendto.ti_1
 * @brief
 *    sendto() successful call
 * @details
 */
TEST_F(udp_sendto, ti_1)
{
    int rc = EOK;
    int fd;
    char buf[] = "hello";

    fd = udp_base::sock_create();
    ASSERT_LE(0, fd);

    errno = EOK;
    rc = bind(fd, (struct sockaddr *)&client_addr, sizeof(client_addr));
    EXPECT_EQ(EOK, errno);
    EXPECT_EQ(0, rc);

    errno = EOK;
    rc = sendto(fd, (void *)buf, sizeof(buf), 0, (struct sockaddr *)&server_addr,
                sizeof(server_addr));
    EXPECT_EQ(EOK, errno);
    EXPECT_EQ(sizeof(buf), static_cast<size_t>(rc));

    close(fd);
}

/**
 * @test udp_sendto.ti_2
 * @brief
 *    sendto() invalid socket fd
 * @details
 */
TEST_F(udp_sendto, ti_2)
{
    int rc = EOK;
    int fd;
    char buf[] = "hello";

    fd = udp_base::sock_create();
    ASSERT_LE(0, fd);

    errno = EOK;
    rc = bind(fd, (struct sockaddr *)&client_addr, sizeof(client_addr));
    EXPECT_EQ(EOK, errno);
    EXPECT_EQ(0, rc);

    errno = EOK;
    rc = sendto(0xFF, (void *)buf, sizeof(buf), 0, (struct sockaddr *)&server_addr,
                sizeof(server_addr));
    EXPECT_EQ(EBADF, errno);
    EXPECT_EQ(-1, rc);

    close(fd);
}

/**
 * @test udp_sendto.ti_3
 * @brief
 *    sendto() invalid buffer length (>65,507 bytes, >65,527 bytes IPv6)
 * @details
 */
TEST_F(udp_sendto, ti_3)
{
    int rc = EOK;
    int fd;
    char buf[65528] = "hello";

    size_t max_possible_size = (client_addr.addr.sa_family == AF_INET ? 65507 : 65527);

    fd = udp_base::sock_create();
    ASSERT_LE(0, fd);

    errno = EOK;
    rc = bind(fd, (struct sockaddr *)&client_addr, sizeof(client_addr));
    EXPECT_EQ(EOK, errno);
    EXPECT_EQ(0, rc);

    errno = EOK;
    rc = sendto(fd, (void *)buf, max_possible_size, 0, (struct sockaddr *)&server_addr,
                sizeof(server_addr));
    EXPECT_EQ(EOK, errno);
    EXPECT_EQ(max_possible_size, static_cast<size_t>(rc));

    errno = EOK;
    rc = sendto(fd, (void *)buf, sizeof(buf), 0, (struct sockaddr *)&server_addr,
                sizeof(server_addr));
    EXPECT_EQ(EMSGSIZE, errno);
    EXPECT_EQ(-1, rc);

    close(fd);
}

/**
 * @test udp_sendto.ti_4
 * @brief
 *    sendto() invalid address length
 * @details
 */
TEST_F(udp_sendto, ti_4)
{
    int rc = EOK;
    int fd;
    char buf[] = "hello";

    fd = udp_base::sock_create();
    ASSERT_LE(0, fd);

    errno = EOK;
    rc = bind(fd, (struct sockaddr *)&client_addr, sizeof(client_addr));
    EXPECT_EQ(EOK, errno);
    EXPECT_EQ(0, rc);

    errno = EOK;
    rc = sendto(fd, (void *)buf, sizeof(buf), 0, (struct sockaddr *)&server_addr,
                sizeof(struct sockaddr) - 1);
    EXPECT_EQ(EINVAL, errno);
    EXPECT_EQ(-1, rc);

    close(fd);
}

/**
 * @test udp_sendto.ti_5
 * @brief
 *    sendto() invalid flag set
 * @details
 */
TEST_F(udp_sendto, ti_5)
{
    int rc = EOK;
    int fd;
    char buf[] = "hello";

    fd = udp_base::sock_create();
    ASSERT_LE(0, fd);

    errno = EOK;
    rc = bind(fd, (struct sockaddr *)&client_addr, sizeof(client_addr));
    EXPECT_EQ(EOK, errno);
    EXPECT_EQ(0, rc);

    errno = EOK;
    rc = sendto(fd, (void *)buf, sizeof(buf), MSG_OOB, (struct sockaddr *)&server_addr,
                sizeof(server_addr));
    if (m_family == PF_INET) {
        EXPECT_EQ(EOPNOTSUPP, errno);
        EXPECT_EQ(-1, rc);
    } else {
        // Apparently IPv6 ignores MSG_OOB
        EXPECT_EQ(EOK, errno);
        EXPECT_EQ(sizeof(buf), static_cast<size_t>(rc));
    }

    close(fd);
}

/**
 * @test udp_sendto.ti_6
 * @brief
 *    sendto() to sero port
 * @details
 */
TEST_F(udp_sendto, ti_6)
{
    int rc = EOK;
    int fd;
    char buf[] = "hello";
    sockaddr_store_t addr;

    fd = udp_base::sock_create();
    ASSERT_LE(0, fd);

    errno = EOK;
    rc = bind(fd, (struct sockaddr *)&client_addr, sizeof(client_addr));
    EXPECT_EQ(EOK, errno);
    EXPECT_EQ(0, rc);

    memcpy(&addr, &server_addr, sizeof(addr));
    sys_set_port((struct sockaddr *)&addr, 0);

    errno = EOK;
    rc = sendto(fd, (void *)buf, sizeof(buf), 0, (struct sockaddr *)&addr, sizeof(addr));
    EXPECT_EQ(EINVAL, errno);
    EXPECT_GT(0, rc);

    close(fd);
}
