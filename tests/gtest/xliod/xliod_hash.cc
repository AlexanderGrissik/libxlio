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

#include "xliod_base.h"

#include "tools/daemon/hash.h"

struct element {
    hash_key_t key;
    int value;
};

class xliod_hash : public ::testing::Test {};

TEST_F(xliod_hash, ti_1)
{
    hash_t ht;
    int reference[] = {3, 5, 107, 199};
    size_t i = 0;

    for (i = 0; i < ARRAY_SIZE(reference); i++) {
        ht = hash_create(NULL, reference[i]);
        ASSERT_TRUE(ht);
        EXPECT_EQ(reference[i], hash_size(ht));
        EXPECT_EQ(0, hash_count(ht));
        hash_destroy(ht);
    }
}

TEST_F(xliod_hash, ti_2)
{
    hash_t ht;
    int reference[] = {4, 12, 100, 200};
    size_t i = 0;

    for (i = 0; i < ARRAY_SIZE(reference); i++) {
        ht = hash_create(NULL, reference[i]);
        ASSERT_FALSE(ht);
    }
}

TEST_F(xliod_hash, ti_3)
{
    hash_t ht;
    struct element element[] = {{12345, 1}, {(hash_key_t)-12345, 2}, {0, 3}};
    size_t i;

    ht = hash_create(NULL, 5);
    ASSERT_TRUE(ht);
    ASSERT_EQ(5, hash_size(ht));

    for (i = 0; i < ARRAY_SIZE(element); i++) {
        EXPECT_TRUE(hash_put(ht, element[i].key, &element[i]));
    }
    EXPECT_EQ(3, hash_count(ht));

    hash_destroy(ht);
}

TEST_F(xliod_hash, ti_4)
{
    hash_t ht;
    struct element element[] = {{12345, 1}, {123, 2}, {12, 3}};
    size_t i;

    ht = hash_create(NULL, 5);
    ASSERT_TRUE(ht);
    ASSERT_EQ(5, hash_size(ht));

    for (i = 0; i < ARRAY_SIZE(element); i++) {
        EXPECT_TRUE(hash_put(ht, element[i].key, &element[i]));
    }
    EXPECT_EQ(3, hash_count(ht));

    for (i = 0; i < ARRAY_SIZE(element); i++) {
        EXPECT_EQ(((uintptr_t)&element[i]), ((uintptr_t)hash_get(ht, element[i].key)));
    }

    hash_destroy(ht);
}

TEST_F(xliod_hash, ti_5)
{
    hash_t ht;
    struct element element[] = {{12345, 1}, {0, 2}, {12, 3}, {77, 4}};
    size_t i;

    ht = hash_create(NULL, 3);
    ASSERT_TRUE(ht);
    ASSERT_EQ(3, hash_size(ht));

    for (i = 0; i < ARRAY_SIZE(element) - 1; i++) {
        EXPECT_TRUE(hash_put(ht, element[i].key, &element[i]));
    }
    EXPECT_EQ(3, hash_count(ht));

    EXPECT_FALSE(hash_put(ht, element[3].key, &element[3]));
    EXPECT_EQ(3, hash_count(ht));

    hash_destroy(ht);
}

TEST_F(xliod_hash, ti_6)
{
    hash_t ht;
    struct element element[] = {{12345, 1}, {0, 2}, {12, 3}};
    struct element *e;
    size_t i;

    ht = hash_create(NULL, 5);
    ASSERT_TRUE(ht);
    ASSERT_EQ(5, hash_size(ht));

    for (i = 0; i < ARRAY_SIZE(element); i++) {
        EXPECT_TRUE(hash_put(ht, element[i].key, &element[i]));
    }
    EXPECT_EQ(3, hash_count(ht));

    element[1].value = 555;
    e = (struct element *)hash_get(ht, element[1].key);
    EXPECT_EQ(((uintptr_t)&element[1]), ((uintptr_t)e));
    EXPECT_EQ(3, hash_count(ht));
    e = (struct element *)hash_get(ht, element[1].key);
    ASSERT_TRUE(e);
    EXPECT_EQ(((uintptr_t)&element[1]), ((uintptr_t)e));
    EXPECT_EQ(555, e->value);

    hash_destroy(ht);
}

TEST_F(xliod_hash, ti_7)
{
    hash_t ht;
    struct element element[] = {{12345, 1}, {123, 2}, {1234, 3}};
    size_t i;

    ht = hash_create(NULL, 5);
    ASSERT_TRUE(ht);
    ASSERT_EQ(5, hash_size(ht));

    for (i = 0; i < ARRAY_SIZE(element); i++) {
        EXPECT_TRUE(hash_put(ht, element[i].key, &element[i]));
    }
    EXPECT_EQ(3, hash_count(ht));

    hash_del(ht, element[1].key);
    EXPECT_EQ(2, hash_count(ht));
    EXPECT_FALSE(hash_get(ht, element[1].key));

    hash_destroy(ht);
}

TEST_F(xliod_hash, ti_8)
{
    hash_t ht;
    struct element element[] = {{12345, 1}, {(hash_key_t)-12345, 2}, {0, 3}};
    size_t i;

    ht = hash_create(NULL, 5);
    ASSERT_TRUE(ht);
    ASSERT_EQ(5, hash_size(ht));

    for (i = 0; i < ARRAY_SIZE(element); i++) {
        EXPECT_TRUE(hash_put(ht, element[i].key, &element[i]));
    }
    EXPECT_EQ(3, hash_count(ht));

    for (i = 0; i < ARRAY_SIZE(element); i++) {
        hash_del(ht, element[i].key);
    }
    EXPECT_EQ(0, hash_count(ht));

    hash_destroy(ht);
}

TEST_F(xliod_hash, ti_9)
{
    hash_t ht;
    struct element element[] = {{12345, 1}, {1234, 2}, {12, 3}};
    struct element *e;
    size_t i;

    ht = hash_create(NULL, 3);
    ASSERT_TRUE(ht);
    ASSERT_EQ(3, hash_size(ht));

    for (i = 0; i < ARRAY_SIZE(element); i++) {
        EXPECT_TRUE(hash_put(ht, element[i].key, &element[i]));
    }
    EXPECT_EQ(3, hash_count(ht));

    for (i = 0; i < 256; i++) {
        hash_del(ht, element[1].key);
        ASSERT_EQ(2, hash_count(ht));

        element[1].value = i;
        e = (struct element *)hash_put(ht, element[1].key, &element[1]);
        ASSERT_TRUE(e);
        ASSERT_EQ(3, hash_count(ht));
        ASSERT_EQ(((uintptr_t)&element[1]), ((uintptr_t)e));

        e = (struct element *)hash_get(ht, element[1].key);
        ASSERT_TRUE(e);
        ASSERT_EQ(((uintptr_t)&element[1]), ((uintptr_t)e));
        ASSERT_EQ(i, static_cast<size_t>(e->value));
    }

    hash_destroy(ht);
}
