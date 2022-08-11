/*
 * Copyright (c) 2001-2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
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

#include <sys/mman.h>
#include "common/def.h"
#include "common/log.h"
#include "common/sys.h"
#include "common/base.h"
#include "src/vma/util/sock_addr.h"
#include "tcp_base.h"

class tcp_accept : public tcp_base {
};

/**
 * @test tcp_accept.mapped_ipv4_accept
 * @brief
 *    IPv6 mapped IPv4 accept
 *
 * @details
 */
TEST_F(tcp_accept, mapped_ipv4_accept)
{
    if (!is_mapped_ipv4_set()) {
        return;
    }

    auto check_accpet = [this](bool api4) {
        int pid = fork();

        if (0 == pid) { // Child
            barrier_fork(pid);

            int fd = tcp_base::sock_create(AF_INET, false);
            EXPECT_LE_ERRNO(0, fd);
            if (0 <= fd) {
                struct sockaddr *cl_addr =
                    reinterpret_cast<struct sockaddr *>(&client_addr_mapped_ipv4);
                struct sockaddr *sr_addr =
                    reinterpret_cast<struct sockaddr *>(&server_addr_mapped_ipv4);

                int rc = bind(fd, cl_addr, sizeof(client_addr_mapped_ipv4));
                EXPECT_EQ_ERRNO(0, rc);
                if (0 == rc) {
                    rc = connect(fd, sr_addr, sizeof(server_addr_mapped_ipv4));
                    EXPECT_EQ_ERRNO(0, rc);
                    if (0 == rc) {
                        log_trace("Established connection: fd=%d to %s from %s\n", fd,
                                  sockaddr2str(sr_addr).c_str(), sockaddr2str(cl_addr).c_str());

                        peer_wait(fd);
                    }
                }

                close(fd);
            }

            // This exit is very important, otherwise the fork
            // keeps running and may duplicate other tests.
            exit(testing::Test::HasFailure());
        } else { // Parent
            sockaddr_store_t any_addr;
            memset(&any_addr, 0, sizeof(any_addr));
            any_addr.addr6.sin6_family = AF_INET6;
            any_addr.addr6.sin6_port = server_addr.addr6.sin6_port;

            int l_fd = tcp_base::sock_create(AF_INET6, false, 10);
            EXPECT_LE_ERRNO(0, l_fd);
            if (0 <= l_fd) {
                int rc = bind(l_fd, reinterpret_cast<const struct sockaddr *>(&any_addr),
                              sizeof(any_addr));
                EXPECT_EQ_ERRNO(0, rc);
                if (0 == rc) {
                    rc = listen(l_fd, 5);
                    EXPECT_EQ_ERRNO(0, rc);
                    if (0 == rc) {
                        barrier_fork(pid);

                        int fd = -1;
                        sockaddr_store_t peer_addr;
                        struct sockaddr *ppeer = reinterpret_cast<struct sockaddr *>(&peer_addr);
                        socklen_t socklen = sizeof(peer_addr);
                        memset(&peer_addr, 0, socklen);
                        if (api4) {
                            fd = accept4(l_fd, ppeer, &socklen, 0);
                        } else {
                            fd = accept(l_fd, ppeer, &socklen);
                        }
                        EXPECT_LE_ERRNO(0, fd);
                        if (0 <= fd) {
                            log_trace("Accepted connection: fd=%d from %s\n", fd,
                                      sockaddr2str(ppeer).c_str());

                            EXPECT_EQ_MAPPED_IPV4(peer_addr.addr6,
                                                  client_addr_mapped_ipv4.addr.sin_addr.s_addr);

                            auto clear_sockaddr = [&socklen, &peer_addr]() {
                                socklen = sizeof(peer_addr);
                                memset(&peer_addr, 0, socklen);
                            };

                            clear_sockaddr();
                            getpeername(fd, ppeer, &socklen);
                            EXPECT_EQ_MAPPED_IPV4(peer_addr.addr6,
                                                  client_addr_mapped_ipv4.addr.sin_addr.s_addr);

                            clear_sockaddr();
                            getsockname(fd, ppeer, &socklen);
                            EXPECT_EQ_MAPPED_IPV4(peer_addr.addr6,
                                                  server_addr_mapped_ipv4.addr.sin_addr.s_addr);

                            close(fd);
                        }
                    }
                }

                close(l_fd);
            }

            EXPECT_EQ(0, wait_fork(pid));
        }
    };

    log_trace("Checking accept()\n");
    check_accpet(false);
    log_trace("Checking accept4()\n");
    check_accpet(true);
}