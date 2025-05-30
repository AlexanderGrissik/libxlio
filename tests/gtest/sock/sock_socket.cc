/*
 * SPDX-FileCopyrightText: NVIDIA CORPORATION & AFFILIATES
 * Copyright (c) 2021-2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: GPL-2.0-only or BSD-2-Clause
 */

#include "common/def.h"
#include "common/log.h"
#include "common/sys.h"
#include "common/base.h"

#include "sock_base.h"

class sock_socket : public sock_base {};

/**
 * @test sock_socket.ti_1
 * @brief
 *    Create UDP socket
 * @details
 */
TEST_F(sock_socket, ti_1)
{
    int fd = UNDEFINED_VALUE;

    errno = EOK;
    fd = socket(m_family, SOCK_DGRAM, IPPROTO_IP);
    EXPECT_LE(0, fd);
    EXPECT_EQ(EOK, errno);

    close(fd);
}

/**
 * @test sock_socket.ti_2
 * @brief
 *    Create TCP socket
 * @details
 */
TEST_F(sock_socket, ti_2)
{
    int fd = UNDEFINED_VALUE;

    errno = EOK;
    fd = socket(m_family, SOCK_STREAM, IPPROTO_IP);
    EXPECT_LE(0, fd);
    EXPECT_EQ(EOK, errno);

    close(fd);
}

/**
 * @test sock_socket.ti_3
 * @brief
 *    Create UNIX socket
 * @details
 */
TEST_F(sock_socket, ti_3)
{
    int fd = UNDEFINED_VALUE;

    errno = EOK;
    fd = socket(PF_UNIX, SOCK_DGRAM, IPPROTO_IP);
    EXPECT_LE(0, fd);
    EXPECT_EQ(EOK, errno);

    close(fd);
}

/**
 * @test sock_socket.ti_4
 * @brief
 *    Create RAW socket
 * @details
 */
TEST_F(sock_socket, ti_4)
{
    int fd = UNDEFINED_VALUE;

    errno = EOK;
    fd = socket(m_family, SOCK_RAW, IPPROTO_TCP);
    if (sys_rootuser()) {
        EXPECT_LE(0, fd);
        EXPECT_EQ(EOK, errno);
    } else {
        EXPECT_EQ(-1, fd);
        EXPECT_EQ(EPERM, errno);
    }

    close(fd);
}

/**
 * @test sock_socket.ti_5
 * @brief
 *    Check domain argument
 * @details
 */
TEST_F(sock_socket, ti_5)
{
    int fd = UNDEFINED_VALUE;

    errno = EOK;
    fd = socket(PF_UNSPEC, SOCK_DGRAM, IPPROTO_IP);
    EXPECT_EQ(-1, fd);
    EXPECT_EQ(EAFNOSUPPORT, errno);

    errno = EOK;
    fd = socket(PF_MAX + 1, SOCK_STREAM, IPPROTO_IP);
    EXPECT_EQ(-1, fd);
    EXPECT_EQ(EAFNOSUPPORT, errno);
}

/**
 * @test sock_socket.ti_6
 * @brief
 *    Check type argument
 * @details
 */
TEST_F(sock_socket, ti_6)
{
    int fd = UNDEFINED_VALUE;

    errno = EOK;
    fd = socket(m_family, 0x10, IPPROTO_IP);
    EXPECT_EQ(-1, fd);
    EXPECT_EQ(EINVAL, errno);
}

/**
 * @test sock_socket.ti_7
 * @brief
 *    Check proto argument
 * @details
 */
TEST_F(sock_socket, ti_7)
{
    int fd = UNDEFINED_VALUE;

    errno = EOK;
    fd = socket(m_family, SOCK_DGRAM, IPPROTO_UDP);
    EXPECT_LE(0, fd);
    EXPECT_EQ(EOK, errno);

    close(fd);

    errno = EOK;
    fd = socket(m_family, SOCK_STREAM, IPPROTO_UDP);
    EXPECT_EQ(-1, fd);
    EXPECT_EQ(EPROTONOSUPPORT, errno);

    close(fd);

    errno = EOK;
    fd = socket(m_family, SOCK_STREAM, IPPROTO_TCP);
    EXPECT_LE(0, fd);
    EXPECT_EQ(EOK, errno);

    close(fd);

    errno = EOK;
    fd = socket(m_family, SOCK_DGRAM, IPPROTO_TCP);
    EXPECT_EQ(-1, fd);
    EXPECT_EQ(EPROTONOSUPPORT, errno);

    close(fd);
}
