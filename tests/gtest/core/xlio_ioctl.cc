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

#if defined(EXTRA_API_ENABLED) && (EXTRA_API_ENABLED == 1)

#include "xlio_base.h"

class xlio_ioctl : public xlio_base {
protected:
    void SetUp()
    {
        uint64_t xlio_extra_api_cap = XLIO_EXTRA_API_IOCTL;

        xlio_base::SetUp();

        SKIP_TRUE((xlio_api->cap_mask & xlio_extra_api_cap) == xlio_extra_api_cap,
                  "This test requires XLIO capabilities as XLIO_EXTRA_API_IOCTL");
    }
    void TearDown() { xlio_base::TearDown(); }
};

/**
 * @test xlio_ioctl.ti_1
 * @brief
 *    CMSG_XLIO_IOCTL_USER_ALLOC command message format check
 * @details
 */
TEST_F(xlio_ioctl, ti_1)
{
    int rc = EOK;
    int fd;
#pragma pack(push, 1)
    struct {
        uint8_t flags;
        void *(*alloc_func)(size_t);
        void (*free_func)(void *);
    } data;
#pragma pack(pop)
    struct cmsghdr *cmsg;
    char cbuf[CMSG_SPACE(sizeof(data))];

    ASSERT_TRUE((sizeof(uint8_t) + sizeof(uintptr_t) + sizeof(uintptr_t)) == sizeof(data));

    /* scenario #1: Wrong cmsg length */
    errno = EOK;
    cmsg = (struct cmsghdr *)cbuf;
    cmsg->cmsg_level = SOL_SOCKET;
    cmsg->cmsg_type = CMSG_XLIO_IOCTL_USER_ALLOC;
    cmsg->cmsg_len = CMSG_LEN(sizeof(data)) - 1;
    data.flags = 0x01;
    data.alloc_func = malloc;
    data.free_func = free;
    memcpy(CMSG_DATA(cmsg), &data, sizeof(data));

    rc = xlio_api->ioctl(cmsg, cmsg->cmsg_len);
    EXPECT_EQ(-1, rc);
    EXPECT_TRUE(EINVAL == errno);

    /* scenario #2: invalid function pointer */
    errno = EOK;
    cmsg = (struct cmsghdr *)cbuf;
    cmsg->cmsg_level = SOL_SOCKET;
    cmsg->cmsg_type = CMSG_XLIO_IOCTL_USER_ALLOC;
    cmsg->cmsg_len = CMSG_LEN(sizeof(data));
    data.flags = 0x01;
    data.alloc_func = malloc;
    data.free_func = NULL;
    memcpy(CMSG_DATA(cmsg), &data, sizeof(data));

    rc = xlio_api->ioctl(cmsg, cmsg->cmsg_len);
    EXPECT_EQ(-1, rc);
    EXPECT_TRUE(EINVAL == errno);

    /* scenario #3: Command can not be used after initialization of internals */
    fd = socket(m_family, SOCK_DGRAM, IPPROTO_IP);
    ASSERT_LE(0, fd);

    errno = EOK;
    cmsg = (struct cmsghdr *)cbuf;
    cmsg->cmsg_level = SOL_SOCKET;
    cmsg->cmsg_type = CMSG_XLIO_IOCTL_USER_ALLOC;
    cmsg->cmsg_len = CMSG_LEN(sizeof(data));
    data.flags = 0x01;
    data.alloc_func = malloc;
    data.free_func = free;
    memcpy(CMSG_DATA(cmsg), &data, sizeof(data));

    rc = xlio_api->ioctl(cmsg, cmsg->cmsg_len);
    EXPECT_EQ(-1, rc);
    EXPECT_TRUE(EINVAL == errno);
}

#endif /* EXTRA_API_ENABLED */
