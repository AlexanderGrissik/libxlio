/*
 * Copyright (c) 2001-2021 Mellanox Technologies, Ltd. All rights reserved.
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

#include <dev/ring_profile.h>

ring_profiles_collection *g_p_ring_profile = NULL;

ring_profile::ring_profile(const xlio_ring_type_attr *ring_desc)
{
    m_ring_desc.comp_mask = ring_desc->comp_mask;
    m_ring_desc.ring_type = ring_desc->ring_type;
    switch (ring_desc->ring_type) {
    case XLIO_RING_PACKET:
        m_ring_desc.ring_pktq.comp_mask = ring_desc->ring_pktq.comp_mask;
        break;
        break;
    default:
        break;
    }
    create_string();
};

const char *ring_profile::get_xlio_ring_type_str()
{
    switch (m_ring_desc.ring_type) {
    case XLIO_RING_PACKET:
        return "XLIO_PKTS_RING";
    default:
        return "";
    }
};

ring_profile::ring_profile()
{
    m_ring_desc.ring_type = XLIO_RING_PACKET;
    m_ring_desc.comp_mask = 0;
    m_ring_desc.ring_pktq.comp_mask = 0;
    create_string();
};

void ring_profile::create_string()
{
    ostringstream s;

    s << get_xlio_ring_type_str();
    m_str = s.str();
}

bool ring_profile::operator==(const xlio_ring_type_attr &p2)
{
    ring_profile other(&p2);

    return (m_str.compare(other.to_str()) == 0);
}

ring_profiles_collection::ring_profiles_collection()
    : m_curr_idx(START_RING_INDEX)
{
}

xlio_ring_profile_key ring_profiles_collection::add_profile(xlio_ring_type_attr *profile)
{
    // first check if this profile exists
    ring_profile_map_t::iterator it = m_profs_map.begin();
    for (; it != m_profs_map.end(); it++) {
        if (*it->second == *profile) {
            return it->first;
        }
    }
    // key 0 is invalid
    xlio_ring_profile_key key = m_curr_idx;
    m_curr_idx++;
    ring_profile *prof = new ring_profile(profile);
    m_profs_map[key] = prof;
    return key;
}

ring_profile *ring_profiles_collection::get_profile(xlio_ring_profile_key key)
{
    ring_profile_map_t::iterator iter = m_profs_map.find(key);
    if (iter != m_profs_map.end()) {
        return iter->second;
    }
    return NULL;
}

ring_profiles_collection::~ring_profiles_collection()
{
    ring_profile_map_t::iterator iter;

    while ((iter = m_profs_map.begin()) != m_profs_map.end()) {
        delete (iter->second);
        m_profs_map.erase(iter);
    }
}
