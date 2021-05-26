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

#ifndef VMA_EXTRA_H
#define VMA_EXTRA_H

#include <stddef.h>
#include <stdint.h>
#include <netinet/in.h>
#include <sys/socket.h>

/*
 * Flags for recvfrom_zcopy()
 */
#define MSG_VMA_ZCOPY_FORCE	0x01000000 // don't fallback to bcopy
#define	MSG_VMA_ZCOPY		0x00040000 // return: zero copy was done

/*
 * Options for setsockopt()/getsockopt()
 */
#define SO_VMA_GET_API          2800
#define SO_VMA_USER_DATA        2801
#define SO_VMA_RING_ALLOC_LOGIC 2810
#define SO_VMA_RING_USER_MEMORY 2811
#define SO_VMA_FLOW_TAG         2820
#define SO_VMA_SHUTDOWN_RX      2821
#define SO_VMA_PD               2822
#define SCM_VMA_PD              SO_VMA_PD

enum {
	CMSG_XLIO_IOCTL_USER_ALLOC = 2900
};

/*
 * Flags for Dummy send API
 */
#define VMA_SND_FLAGS_DUMMY MSG_SYN // equals to 0x400


/* 
 * Return values for the receive packet notify callback function
 */
typedef enum {
	VMA_PACKET_DROP,     /* VMA will drop the received packet and recycle 
	                        the buffer if no other socket needs it */

	VMA_PACKET_RECV,     /* VMA will queue the received packet on this socket ready queue.
	                        The application will read it with the usual recv socket APIs */

	VMA_PACKET_HOLD      /* Application will handle the queuing of the received packet. The application
	                        must return the descriptor to VMA using the free_packet function
				But not in the context of VMA's callback itself. */
} vma_recv_callback_retval_t;

/**
 * @brief Pass this structure as an argument into getsockopt() with @ref SO_VMA_PD
 * 	to get protection domain information from ring used for current socket.
 * 	This information can be available after setting connection for TX ring
 * 	and bounding to device for RX ring.
 * 	By default getting PD for TX ring.
 * 	This case can be used with sendmsg(SCM_VMA_PD) when the data portion contains
 * 	an array of the elements with datatype as struct vma_pd_key. Number of elements in this
 * 	array should be equal to msg_iovlen value. Every data pointer in msg_iov has
 * 	correspondent memory key.
 *
 * @param flags - to specify needed information.
 * @param pd - protection domain (PD) for the RDMA device context
 */
struct vma_pd_attr {
	uint32_t flags;
	void*	 ib_pd;
};

/**
 * @brief elements with this datatype can be passed into sendmsg(SCM_VMA_PD)
 * as control message with correspondent pointer to data.
 *
 * @param flags - to specify needed information. By default mkey value is used.
 * @param mkey - memory key
 */
struct vma_pd_key {
	uint32_t flags;
	uint32_t mkey;
};

/************ SocketXtreme API types definition start***************/

typedef enum {
    VMA_SOCKETXTREME_PACKET 			= (1ULL << 32), /* New packet is available */
    VMA_SOCKETXTREME_NEW_CONNECTION_ACCEPTED	= (1ULL << 33)  /* New connection is auto accepted by server */
} vma_socketxtreme_events_t;

/*
 * Represents  VMA buffer
 * Used in SocketXtreme extended API.
 */
struct vma_buff_t {
	struct vma_buff_t*	next;		/* next buffer (for last buffer next == NULL) */
	void*		payload;		/* pointer to data */
	uint16_t	len;			/* data length */
};

/**
 * Represents one VMA packet
 * Used in SocketXtreme extended API.
 */
struct vma_packet_desc_t {
	size_t			num_bufs;	/* number of packet's buffers */
	uint16_t		total_len;	/* total data length */
	struct vma_buff_t*	buff_lst;	/* list of packet's buffers */
	struct timespec 	hw_timestamp;	/* packet hw_timestamp */
};

/*
 * Represents VMA Completion.
 * Used in SocketXtreme extended API.
 */
struct vma_completion_t {
	/* Packet is valid in case VMA_SOCKETXTREME_PACKET event is set
	 */
	struct vma_packet_desc_t packet;
	/* Set of events
	 */
	uint64_t events;
	/* User provided data.
	 * By default this field has FD of the socket
	 * User is able to change the content using setsockopt()
	 * with level argument SOL_SOCKET and opname as SO_VMA_USER_DATA
	 */
	uint64_t                 user_data;
	/* Source address (in network byte order) set for:
	 * VMA_SOCKETXTREME_PACKET and VMA_SOCKETXTREME_NEW_CONNECTION_ACCEPTED events
	 */
	struct sockaddr_in       src;
	/* Connected socket's parent/listen socket fd number.
	 * Valid in case VMA_SOCKETXTREME_NEW_CONNECTION_ACCEPTED event is set.
	 */
	int 			listen_fd;
};

/************ SocketXtreme API types definition end ***************/

/**
 * Represents one VMA packets 
 * Used in zero-copy extended API.
 */
struct __attribute__ ((packed)) vma_packet_t {
	void*		packet_id;		// packet identifier
	size_t		sz_iov;			// number of fragments
	struct iovec	iov[];			// fragments size+data
};

/**
 * Represents received packets in VMA
 * Used in zero-copy extended API.
 */
struct __attribute__ ((packed)) vma_packets_t {
	size_t n_packet_num;		// number of received packets
	struct vma_packet_t	pkts[];	// array of received packets
};

/* 
 * Structure holding additional information on the packet and socket
 * Note: Check structure size value for future VMA libraries changes
 */
struct __attribute__ ((packed)) vma_info_t {
	size_t 			struct_sz;	/* Compare this value with sizeof(vma_info_t) to check version compatability */
	void*			packet_id;	/* VMA's handle to received packet buffer to be return if zero copy logic is used */

	/* Packet addressing information (in network byte order) */
	struct sockaddr_in*	src;
	struct sockaddr_in*	dst;

	/* Packet information */
	size_t			payload_sz;

	/* Socket's information */
	uint32_t		socket_ready_queue_pkt_count;	/* Current count of packets waiting to be read from the socket */
	uint32_t		socket_ready_queue_byte_count;	/* Current count of bytes waiting to be read from the socket */

	/* Packet timestamping information */
	struct timespec		hw_timestamp;
	struct timespec		sw_timestamp;
};

struct vma_rate_limit_t {
	uint32_t rate;				/* rate limit in Kbps */
	uint32_t max_burst_sz;			/* maximum burst size in bytes */
	uint16_t typical_pkt_sz;		/* typical packet size in bytes */
};

typedef int vma_ring_profile_key;

typedef enum {
	RING_LOGIC_PER_INTERFACE = 0,            //!< RING_LOGIC_PER_INTERFACE
	RING_LOGIC_PER_IP = 1,                   //!< RING_LOGIC_PER_IP
	RING_LOGIC_PER_SOCKET = 10,              //!< RING_LOGIC_PER_SOCKET
	RING_LOGIC_PER_USER_ID = 11,             //!< RING_LOGIC_PER_USER_ID
	RING_LOGIC_PER_THREAD = 20,              //!< RING_LOGIC_PER_THREAD
	RING_LOGIC_PER_CORE = 30,                //!< RING_LOGIC_PER_CORE
	RING_LOGIC_PER_CORE_ATTACH_THREADS = 31, //!< RING_LOGIC_PER_CORE_ATTACH_THREADS
	RING_LOGIC_LAST                          //!< RING_LOGIC_LAST
} ring_logic_t;

typedef enum {
	VMA_RING_ALLOC_MASK_RING_PROFILE_KEY = (1 << 0),
	VMA_RING_ALLOC_MASK_RING_USER_ID = (1 << 1),
	VMA_RING_ALLOC_MASK_RING_INGRESS = (1 << 2),
	VMA_RING_ALLOC_MASK_RING_ENGRESS = (1 << 3),
} vma_ring_alloc_logic_attr_comp_mask;

/**
 * @brief pass this struct to vma using setsockopt with @ref SO_VMA_RING_ALLOC_LOGIC
 * 	to set the allocation logic of this FD when he requests a ring.
 * 	@note ring_alloc_logic is a mandatory
 * @param comp_mask - what fields are read when processing this struct
 * 	see @ref vma_ring_alloc_logic_attr_comp_mask
 * @param ring_alloc_logic- allocation ratio to use
 * @param ring_profile_key - what ring profile to use - get the profile when
 * 	creating ring using @ref vma_add_ring_profile in extra_api
 * 	can only be set once
 * @param user_idx - when used RING_LOGIC_PER_USER_ID int @ref ring_alloc_logic
 * 	this is the user id to define. This lets you define the same ring for
 * 	few FD's regardless the interface\thread\core.
 * @param ingress - RX ring
 * @param engress - TX ring
 */
struct vma_ring_alloc_logic_attr {
	uint32_t	comp_mask;
	ring_logic_t	ring_alloc_logic;
	uint32_t	ring_profile_key;
	uint32_t	user_id;
	uint32_t	ingress:1;
	uint32_t	engress:1;
	uint32_t	reserved:30;
};

struct vma_packet_queue_ring_attr {
	uint32_t	comp_mask;
};

typedef enum {
	// for future use
	VMA_RING_ATTR_LAST
} vma_ring_type_attr_mask;

typedef enum {
	VMA_RING_PACKET,
} vma_ring_type;

/**
 * @param comp_mask - what fields are read when processing this struct
 * 	see @ref vma_ring_type_attr_mask
 * @param ring_type - use cyclic buffer ring or default packets ring
 *
 */
struct vma_ring_type_attr {
	uint32_t	comp_mask;
	vma_ring_type	ring_type;
	union {
		struct vma_packet_queue_ring_attr	ring_pktq;
	};
};

typedef enum {
	VMA_EXTRA_API_REGISTER_RECV_CALLBACK         = (1 << 0),
	VMA_EXTRA_API_RECVFROM_ZCOPY                 = (1 << 1),
	VMA_EXTRA_API_FREE_PACKETS                   = (1 << 2),
	VMA_EXTRA_API_ADD_CONF_RULE                  = (1 << 3),
	VMA_EXTRA_API_THREAD_OFFLOAD                 = (1 << 4),
	VMA_EXTRA_API_GET_SOCKET_RINGS_NUM           = (1 << 5),
	VMA_EXTRA_API_GET_SOCKET_RINGS_FDS           = (1 << 6),
	VMA_EXTRA_API_SOCKETXTREME_POLL              = (1 << 7),
	VMA_EXTRA_API_SOCKETXTREME_FREE_VMA_PACKETS  = (1 << 8),
	VMA_EXTRA_API_SOCKETXTREME_REF_VMA_BUFF      = (1 << 9),
	VMA_EXTRA_API_SOCKETXTREME_FREE_VMA_BUFF     = (1 << 10),
	VMA_EXTRA_API_DUMP_FD_STATS                  = (1 << 11),
	VMA_EXTRA_API_ADD_RING_PROFILE               = (1 << 12),
	VMA_EXTRA_API_IOCTL                          = (1 << 13),
} vma_extra_api_mask;

/** 
 *  
 * VMA Notification callback for incoming packet on socket
 * @param fd Socket's file descriptor which this packet refers to
 * @param iov iovector structure array point holding the packet 
 *            received data buffer pointers and size of each buffer
 * @param iov_sz Size of iov array
 * @param vma_info Additional information on the packet and socket
 * @param context User-defined value provided during callback 
 *                registration for each socket
 *
 *   This callback function should be registered with VMA by calling
 * register_recv_callback() in the extended API. It can be unregistered by 
 * setting a NULL function pointer. VMA will call the callback to notify 
 * of new incoming packets after the IP & UDP header processing and before 
 * they are queued in the socket's receive queue. 
 *   Context of the callback will always be from one of the user's application
 * threads when calling the following socket APIs: select, poll, epoll, recv, 
 * recvfrom, recvmsg, read, readv. 
 * 
 * Notes:
 * - The application can call all of the Socket APIs control and send from
 *   within the callback context.
 * - Packet loss might occur depending on the applications behavior in the 
 *   callback context.
 * - Parameters `iov' and `vma_info' are only valid until callback context 
 *   is returned to VMA. User should copy these structures for later use 
 *   if working with zero copy logic.
 */
typedef vma_recv_callback_retval_t 
(*vma_recv_callback_t)(int fd, size_t sz_iov, struct iovec iov[],
                        struct vma_info_t* vma_info, void *context);

/**
 * VMA Extended Socket API
 */
struct __attribute__ ((packed)) vma_api_t {

	/**
	 * Used to identify which methods were initialized by VMA as part of vma_get_api().
	 * The value content is based on vma_extra_api_mask enum.
	 * Order of fields in this structure should not be changed to keep abi compatibility.
	 */
	uint64_t vma_extra_supported_mask;

	/**
	 * Register a received packet notification callback.
	 * 
	 * @param s Socket file descriptor.
	 * @param callback Callback function.
	 * @param context user contex for callback function.
	 * @return 0 - success, -1 - error
	 * 
	 * errno is set to: EINVAL - not VMA offloaded socket 
	 */
	int (*register_recv_callback)(int s, vma_recv_callback_t callback, void *context);
	
	/**
	 * Zero-copy revcfrom implementation.
	 * 
	 * @param s Socket file descriptor.
	 * @param buf Buffer to fill with received data or pointers to data (see below).
	 * @param flags Pointer to flags (see below).
	 * @param from If not NULL, will be filled with source address (same as recvfrom).
	 * @param fromlen If not NULL, will be filled with source address size (same as recvfrom).
	 * 
	 * This function attempts to receive a packet without doing data copy.
	 * The flags argument can contain the usual flags of recvmsg(), and also the
	 * MSG_VMA_ZCOPY_FORCE flag. If the latter is set, the function will not
	 * fall back to data copy. Otherwise, the function falls back to data copy
	 * if zero-copy cannot be performed. If zero-copy is done then MSG_VMA_ZCOPY
	 * flag is set upon exit.
	 * 
	 * If zero copy is performed (MSG_VMA_ZCOPY flag is returned), the buffer 
	 * is filled with a vma_packets_t structure, holding as much fragments 
	 * as `len' allows. The total size of all fragments is returned.
	 * Otherwise the MSG_VMA_ZCOPY flag is not set and the buffer is filled
	 * with actual data and it's size is returned (same as recvfrom())
	 * If no data was received the return value is zero.
	 * 
	 * NOTE: The returned packet must be freed with free_packet() after
	 * the application finished using it.
	 */
	int (*recvfrom_zcopy)(int s, void *buf, size_t len, int *flags,
                              struct sockaddr *from, socklen_t *fromlen);
	
	/**
	 * Frees a packet received by recvfrom_zcopy() or held by receive callback.
	 * 
	 * @param s Socket from which the packet was received.
	 * @param pkts Array of packet.
	 * @param count Number of packets in the array.
	 * @return 0 on success, -1 on failure
	 * 
	 * errno is set to: EINVAL - not a VMA offloaded socket
	 *                  ENOENT - the packet was not received from `s'.
	 */
	int (*free_packets)(int s, struct vma_packet_t *pkts, size_t count);

	/*
	 * Add a libxlio.conf rule to the top of the list.
	 * This rule will not apply to existing sockets which already considered the conf rules.
	 * (around connect/listen/send/recv ..)
	 * @param config_line A char buffer with the exact format as defined in libxlio.conf, and should end with '\0'.
	 * @return 0 on success, or error code on failure.
	 */
	int (*add_conf_rule)(const char *config_line);

	/*
	 * Create sockets on pthread tid as offloaded/not-offloaded.
	 * This does not affect existing sockets.
	 * Offloaded sockets are still subject to libxlio.conf rules.
	 * @param offload 1 for offloaded, 0 for not-offloaded.
	 * @return 0 on success, or error code on failure.
	 */
	int (*thread_offload)(int offload, pthread_t tid);

	/**
	 * Returns the amount of rings that are associated with socket.
	 *
	 * @param fd File Descriptor number of the socket.
	 * @return On success, return the amount of rings.
	 *         On error, -1 is returned.
	 *
	 * errno is set to: EINVAL - not a VMA offloaded fd
	 */
	int (*get_socket_rings_num)(int fd);

	/**
	 * Returns FDs of the RX rings that are associated with the socket.
	 *
	 * This function gets socket FD + int array + array size and populates
	 * the array with FD numbers of the rings that are associated
	 * with the socket.
	 *
	 * @param fd File Descriptor number.
	 * @param ring_fds Array of ring fds
	 * @param ring_fds_sz Size of the array
	 * @return On success, return the number populated array entries.
	 *         On error, -1 is returned.
	 *
	 * errno is set to: EINVAL - not a VMA offloaded fd + TBD
	 */
	int (*get_socket_rings_fds)(int fd, int *ring_fds, int ring_fds_sz);

	/**
	 * socketxtreme_poll() polls for VMA completions
	 *
	 * @param fd File descriptor.
	 * @param completions VMA completions array.
	 * @param ncompletions Maximum number of completion to return.
	 * @param flags Flags.
	 * @return On success, return the number of ready completions.
	 * 	   On error, -1 is returned, and TBD:errno is set?.
	 *
	 * This function polls the `fd` for VMA completions and returns maximum `ncompletions` ready
	 * completions via `completions` array.
	 * The `fd` can represent a ring, socket or epoll file descriptor.
	 *
	 * VMA completions are indicated for incoming packets and/or for other events.
	 * If VMA_SOCKETXTREME_PACKET flag is enabled in vma_completion_t.events field
	 * the completion points to incoming packet descriptor that can be accesses
	 * via vma_completion_t.packet field.
	 * Packet descriptor points to VMA buffers that contain data scattered
	 * by HW, so the data is deliver to application with zero copy.
	 * Notice: after application finished using the returned packets
	 * and their buffers it must free them using socketxtreme_free_vma_packets(),
	 * socketxtreme_free_vma_buff() functions.
	 *
	 * If VMA_SOCKETXTREME_PACKET flag is disabled vma_completion_t.packet field is
	 * reserved.
	 *
	 * In addition to packet arrival event (indicated by VMA_SOCKETXTREME_PACKET flag)
	 * VMA also reports VMA_SOCKETXTREME_NEW_CONNECTION_ACCEPTED event and standard
	 * epoll events via vma_completion_t.events field.
	 * VMA_SOCKETXTREME_NEW_CONNECTION_ACCEPTED event is reported when new connection is
	 * accepted by the server.
	 * When working with socketxtreme_poll() new connections are accepted
	 * automatically and accept(listen_socket) must not be called.
	 * VMA_SOCKETXTREME_NEW_CONNECTION_ACCEPTED event is reported for the new
	 * connected/child socket (vma_completion_t.user_data refers to child socket)
	 * and EPOLLIN event is not generated for the listen socket.
	 * For events other than packet arrival and new connection acceptance
	 * vma_completion_t.events bitmask composed using standard epoll API
	 * events types.
	 * Notice: the same completion can report multiple events, for example
	 * VMA_SOCKETXTREME_PACKET flag can be enabled together with EPOLLOUT event,
	 * etc...
	 *
	 * * errno is set to: EOPNOTSUPP - socketXtreme was not enabled during configuration time.
	 */
	int (*socketxtreme_poll)(int fd, struct vma_completion_t* completions, unsigned int ncompletions, int flags);

	/**
	 * Frees packets received by socketxtreme_poll().
	 *
	 * @param packets Packets to free.
	 * @param num Number of packets in `packets` array
	 * @return 0 on success, -1 on failure
	 *
	 * For each packet in `packet` array this function:
	 * - Updates receive queue size and the advertised TCP
	 *   window size, if needed, for the socket that received
	 *   the packet.
	 * - Frees vma buffer list that is associated with the packet.
	 *   Notice: for each buffer in buffer list VMA decreases buffer's
	 *   reference count and only buffers with reference count zero are deallocated.
	 *   Notice:
	 *   - Application can increase buffer reference count,
	 *     in order to hold the buffer even after socketxtreme_free_vma_packets()
	 *     was called for the buffer, using socketxtreme_ref_vma_buff().
	 *   - Application is responsible to free buffers, that
	 *     couldn't be deallocated during socketxtreme_free_vma_packets() due to
	 *     non zero reference count, using socketxtreme_free_vma_buff() function.
	 *
	 * errno is set to: EINVAL - NULL pointer is provided.
	 *                  EOPNOTSUPP - socketXtreme was not enabled during configuration time.
	 */
	int (*socketxtreme_free_vma_packets)(struct vma_packet_desc_t *packets, int num);

	/* This function increments the reference count of the buffer.
	 * This function should be used in order to hold the buffer
	 * even after socketxtreme_free_vma_packets() call.
	 * When buffer is not needed any more it should be freed via
	 * socketxtreme_free_vma_buff().
	 *
	 * @param buff Buffer to update.
	 * @return On success, return buffer's reference count after the change
	 * 	   On errors -1 is returned
	 *
	 * errno is set to: EINVAL - NULL pointer is provided.
	 *                  EOPNOTSUPP - socketXtreme was not enabled during configuration time.
	 */
	int (*socketxtreme_ref_vma_buff)(struct vma_buff_t *buff);

	/* This function decrements the buff reference count.
	 * When buff's reference count reaches zero, the buff is
	 * deallocated.
	 *
	 * @param buff Buffer to free.
	 * @return On success, return buffer's reference count after the change
	 * 	   On error -1 is returned
	 *
	 * Notice: return value zero means that buffer was deallocated.
	 *
	 * errno is set to: EINVAL - NULL pointer is provided.
	 *                  EOPNOTSUPP - socketXtreme was not enabled during configuration time.
	 */
	int (*socketxtreme_free_vma_buff)(struct vma_buff_t *buff);

	/*
	 * Dump fd statistics using VMA logger.
	 * @param fd to dump, 0 for all open fds.
	 * @param log_level dumping level corresponding vlog_levels_t enum (vlogger.h).
	 * @return 0 on success, or error code on failure.
	 *
	 * errno is set to: EOPNOTSUPP - Function is not supported when socketXtreme is enabled.
	 */
	int (*dump_fd_stats)(int fd, int log_level);

	/**
	 * add a ring profile to VMA ring profile list. you can use this
	 * to create advacned rings like MP_RQ ring
	 * the need to pass vma the ring profile using the fd's setsockopt
	 * @param profile the profile to add to the list
	 * @param key - the profile key
	 * @return 0 on success -1 on failure
	 */
	int (*vma_add_ring_profile)(struct vma_ring_type_attr *profile, int *key);

	/**
	 * This function allows to communicate with library using extendable protocol
	 * based on struct cmshdr.
	 *
	 * Ancillary data is a sequence of cmsghdr structures with appended data.
	 * The sequence of cmsghdr structures should never be accessed directly.
	 * Instead, use only the following macros: CMSG_ALIGN, CMSG_SPACE, CMSG_DATA,
	 * CMSG_LEN.
	 *
	 * @param cmsg_hdr - point to control message
	 * @param cmsg_len - the byte count of the ancillary data,
	 *                   which contains the size of the structure header.
	 *
	 * @return -1 on failure and 0 on success
	 */
	int (*ioctl)(void *cmsg_hdr, size_t cmsg_len);
};

/**
 * Retrieve VMA extended API.
 * This function can be called as an alternative to getsockopt() call
 * when library is preloaded using LD_PRELOAD
 * getsockopt() call should be used in case application loads library
 * using dlopen()/dlsym().
 *
 * @return Pointer to the VMA Extended Socket API, of NULL if VMA not found. 
 */
static inline struct vma_api_t* vma_get_api()
{
	struct vma_api_t *api_ptr = NULL;
	socklen_t len = sizeof(api_ptr);

	/* coverity[negative_returns] */
	int err = getsockopt(-1, SOL_SOCKET, SO_VMA_GET_API, &api_ptr, &len);
	if (err < 0) {
		return NULL;
	}
	return api_ptr;
}

#endif /* VMA_EXTRA_H */
