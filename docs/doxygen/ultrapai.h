/**
 * @defgroup xlio_ultra_api XLIO Ultra API
 * @brief High-performance zero-copy networking interface
 *
 * The XLIO Ultra API is a performance-oriented, event-based networking interface
 * designed for applications requiring maximum throughput and minimal latency.
 * It provides zero-copy capabilities and efficient memory management for
 * high-performance networking.
 *
 * @section features Key Features
 * - Native zero-copy TX and RX operations
 * - Immediate callback-based event notification without accumulation
 * - Optimized data path with fewer corner cases and non-performance-oriented features
 *   - No blocking mode
 *   - No partial writes
 * - Simplified application development:
 *   - Fewer error conditions and corner cases to handle
 *   - Flexible control of TX data aggregation
 *   - High-level TX operation completion
 * - Concurrency and scalability:
 *   - No global namespace - sockets grouped by polling groups
 *   - Clear concurrency boundaries and scalability model
 *   - Each group can be handled independently by different threads
 *
 * @section architecture Architecture Overview
 * The API is built around three main concepts:
 * 1. **Polling Groups**: Event management and callback registration
 * 2. **Sockets**: TCP socket abstraction with zero-copy capabilities
 * 3. **Buffers**: Memory management for zero-copy operations
 *
 * @section workflow Typical Workflow
 * 1. Initialize XLIO with xlio_init_ex()
 * 2. Create polling group with xlio_poll_group_create()
 * 3. Create socket with xlio_socket_create()
 * 4. Configure socket (bind, connect, listen)
 * 5. Poll for events with xlio_poll_group_poll()
 * 6. Handle events via registered callbacks
 * 7. Send/receive data using zero-copy operations
 * 8. Clean up resources
 *
 * @section concurrency Concurrency and Thread Safety
 * The XLIO Ultra API is designed for high-performance applications with specific
 * concurrency patterns and thread safety requirements.
 *
 * @subsection thread_safety Thread Safety Model
 * - **The API is NOT thread-safe by default**
 * - Applications are responsible for proper serialization when accessing
 *   XLIO objects from multiple threads
 * - No internal locking is provided to maximize performance
 *
 * @subsection polling_group_concurrency Polling Group Concurrency
 * Polling groups are the primary mechanism for achieving concurrency:
 * - **Multiple polling groups can be polled concurrently** from different threads
 * - **Polling groups do not share resources** with each other
 * - **Sockets from different groups can be handled concurrently** without serialization
 *
 * @subsection serialization_requirements Serialization Requirements
 * - **Within a polling group**: All operations require serialization
 *   - Only one thread should call xlio_poll_group_poll() per group at a time
 *   - Socket operations within the same group must be serialized
 *   - Serialized polling group and socket calls can be executed by different threads
 * - **Across polling groups**: No serialization required
 *   - Different threads can operate on different groups simultaneously
 *
 * @subsection thread_safety_exceptions Thread Safety Exceptions
 * Some operations have specific thread safety characteristics:
 * - **Initialization**: xlio_init_ex() and xlio_exit() are not thread-safe
 * - A group created with the flag XLIO_GROUP_FLAG_SAFE can execute a polling and socket TX
 *   operations concurrently
 *
 * @section limitations Current Limitations
 * - TCP sockets only (no UDP support)
 * - No crypto offload support
 * - No bonding support
 * - Only busy polling is supported
 * - fork() is supported only without created polling groups
 * @{
 */
 
/**
 * @defgroup xlio_init Initialization and Cleanup
 * @brief Functions for initializing and cleaning up the XLIO Ultra API
 * @{
 */
 
/* Forward declaration. */
struct ibv_pd;
 
/**
 * @brief Initialize the XLIO Ultra API
 *
 * This function must be called before using any other XLIO Ultra API functions.
 * It's a heavy operation that sets up the internal state, allocates resources,
 * and configures the system for high-performance networking.
 *
 * @note This function is not thread-safe. However, subsequent serialized calls
 * will exit successfully without performing any action.
 *
 * @param attr Initialization attributes structure
 * @return 0 on success, -1 on error (errno is set)
 *
 * @par Error Codes:
 * - EINVAL: Invalid parameters
 * - ENOMEM: Insufficient memory
 * - ENODEV: No compatible network devices found
 *
 * @see xlio_exit()
 * @see xlio_init_attr
 */
int xlio_init_ex(const struct xlio_init_attr *attr);
 
/**
 * @brief Initialize XLIO
 *
 * This function is similar to xlio_init_ex() but doesn't accept additional
 * attributes.
 *
 * @return 0 on success, -1 on error (errno is set)
 *
 * @par Error Codes:
 * - EINVAL: Invalid parameters
 * - ENOMEM: Insufficient memory
 * - ENODEV: No compatible network devices found
 * - EEXIST: XLIO is already initialized
 *
 * @see xlio_exit()
 */
int xlio_init(void);
 
/**
 * @brief Finalize XLIO
 *
 * Finalizes and cleans XLIO resources.
 *
 * @return 0 on success, -1 on error (errno is set)
 */
int xlio_exit(void);
 
/** @} */ // end of xlio_init group
 
/**
 * @defgroup xlio_poll_group Polling Groups
 * @brief Functions for managing polling groups and event handling
 *
 * Polling groups are the core event management mechanism in the XLIO Ultra API.
 * They allow applications to register event callbacks and efficiently poll for
 * network events across multiple sockets.
 *
 * Polling group is a collection of sockets and resources required for their operation.
 * Different polling groups can be used concurrently without serialization.
 *
 * Polling groups provide loggical sockets organization for the following purposes:
 *  - Achieving concurrency and scaling
 *  - Implementing different RX / completion logic
 *
 * Recommendations:
 *  - Groups are expected to be long lived objects. Frequent creation/destruction has a penalty.
 *  - Reduce the number of different network interfaces within a group to minimum. This will
 *    optimize the HW objects utilization. However, maintaining extra groups can have an overhead.
 *
 * @{
 */
 
/**
 * @brief Create a new polling group
 *
 * Creates a new polling group with the specified attributes. Event callbacks
 * are registered per group, allowing applications to implement different
 * handling logic for different types of connections.
 *
 * @param attr Polling group attributes
 * @param group_out Pointer to store the created group handle
 * @return 0 on success, -1 on error (errno is set)
 *
 * @par Error Codes:
 * - EINVAL: Invalid parameters (group_out is NULL, attr is NULL, or socket_event_cb is NULL)
 * - ENOMEM: Insufficient memory
 *
 * @note socket_event_cb is mandatory.
 *
 * @see xlio_poll_group_destroy()
 * @see xlio_poll_group_attr
 */
int xlio_poll_group_create(const struct xlio_poll_group_attr *attr, xlio_poll_group_t *group_out);
 
/**
 * @brief Destroy a polling group
 *
 * Destroys the specified polling group and frees associated resources.
 * All leftover sockets associated with this group are destroyed implicitly.
 *
 * @param group The polling group to destroy
 * @return 0 on success, -1 on error
 */
int xlio_poll_group_destroy(xlio_poll_group_t group);
 
/**
 * @brief Update polling group attributes
 *
 * Updates the attributes of an existing polling group. This allows changing
 * callback functions or flags without recreating the group.
 *
 * @param group The polling group to update
 * @param attr New attributes for the group
 * @return 0 on success, -1 on error (errno is set)
 *
 * @par Error Codes:
 * - EINVAL: Invalid parameters (attr is NULL or socket_event_cb is NULL)
 */
int xlio_poll_group_update(xlio_poll_group_t group, const struct xlio_poll_group_attr *attr);
 
/**
 * @brief Poll for events on a polling group
 *
 * This is the main event processing function. It polls hardware for events,
 * executes TCP timers, and invokes registered callbacks. Most network events
 * are processed from the context of this call.
 *
 * @param group The polling group to poll
 *
 * @note This function should be called regularly in the main event loop.
 * It's non-blocking and will return immediately if no events are available.
 */
void xlio_poll_group_poll(xlio_poll_group_t group);
 
/** @} */ // end of xlio_poll_group group
 
/**
 * @defgroup xlio_socket Socket Management
 * @brief Functions for creating and managing XLIO sockets
 *
 * XLIO sockets are high-performance TCP socket abstractions that provide
 * zero-copy capabilities. They are represented by opaque handles rather than
 * file descriptors.
 *
 * @{
 */
 
/**
 * @brief Create a new XLIO socket
 *
 * Creates a new XLIO socket with the specified attributes. The socket is
 * automatically associated with the specified polling group and configured
 * for high-performance operation.
 *
 * @param attr Socket attributes
 * @param sock_out Pointer to store the created socket handle
 * @return 0 on success, -1 on error (errno is set)
 *
 * @par Error Codes:
 * - EINVAL: Invalid parameters (sock_out is NULL, attr is NULL, group is invalid,
 *           or domain is not AF_INET/AF_INET6)
 * - ENOMEM: Insufficient memory
 * - EMFILE: Too many open files
 *
 * @see xlio_socket_destroy()
 * @see xlio_socket_attr
 */
int xlio_socket_create(const struct xlio_socket_attr *attr, xlio_socket_t *sock_out);
 
/**
 * @brief Destroy an XLIO socket
 *
 * Initiates the socket closing procedure. The process may be asynchronous,
 * and socket events may continue to arrive until the XLIO_SOCKET_EVENT_TERMINATED
 * event is received.
 *
 * @param sock The socket to destroy
 * @return 0 on success, -1 on error (errno is set)
 *
 * @par Error Codes:
 * - EINVAL: Invalid socket handle
 *
 * @note Zero-copy completion events may still arrive after calling this function
 * until the TERMINATED event is received.
 */
int xlio_socket_destroy(xlio_socket_t sock);
 
/**
 * @brief Update socket attributes
 *
 * Updates the flags and user data associated with a socket. This allows
 * changing socket behavior and context without recreating the socket.
 *
 * @param sock The socket to update
 * @param flags New flags for the socket
 * @param userdata_sq New user data for the socket
 * @return 0 on success, -1 on error
 */
int xlio_socket_update(xlio_socket_t sock, unsigned flags, uintptr_t userdata_sq);
 
/**
 * @brief Set socket options
 *
 * Sets socket options, similar to the standard setsockopt() function.
 * Supports standard socket options as well as XLIO-specific options.
 *
 * @param sock The socket to configure
 * @param level The protocol level (SOL_SOCKET, IPPROTO_TCP, etc.)
 * @param optname The option name
 * @param optval Pointer to the option value
 * @param optlen Length of the option value
 * @return 0 on success, -1 on error (errno is set)
 *
 * @see setsockopt(2)
 */
int xlio_socket_setsockopt(xlio_socket_t sock, int level, int optname, const void *optval,
                           socklen_t optlen);
 
/**
 * @brief Get socket name
 *
 * Retrieves the local address of the socket, similar to getsockname().
 *
 * @param sock The socket to query
 * @param addr Buffer to store the address
 * @param addrlen Pointer to the address length
 * @return 0 on success, -1 on error (errno is set)
 *
 * @see getsockname(2)
 */
int xlio_socket_getsockname(xlio_socket_t sock, struct sockaddr *addr, socklen_t *addrlen);
 
/**
 * @brief Get peer name
 *
 * Retrieves the remote address of the socket, similar to getpeername().
 *
 * @param sock The socket to query
 * @param addr Buffer to store the address
 * @param addrlen Pointer to the address length
 * @return 0 on success, -1 on error (errno is set)
 *
 * @see getpeername(2)
 */
int xlio_socket_getpeername(xlio_socket_t sock, struct sockaddr *addr, socklen_t *addrlen);
 
/**
 * @brief Bind socket to address
 *
 * Binds the socket to a local address, similar to bind().
 *
 * @param sock The socket to bind
 * @param addr The address to bind to
 * @param addrlen Length of the address
 * @return 0 on success, -1 on error (errno is set)
 *
 * @par Error Codes:
 * - ENODEV: Trying to bind to a non-NVIDIA NIC
 * - Inherits bind(2) error codes
 *
 * @see bind(2)
 */
int xlio_socket_bind(xlio_socket_t sock, const struct sockaddr *addr, socklen_t addrlen);
 
/**
 * @brief Connect socket to remote address
 *
 * Initiates a connection to a remote address. The operation is non-blocking,
 * and the connection status is reported via the socket event callback.
 *
 * @param sock The socket to connect
 * @param to The remote address to connect to
 * @param tolen Length of the remote address
 * @return 0 on success, -1 on error (errno is set)
 *
 * @par Error Codes:
 * - EISCONN: The socket is already connected
 * - EALREADY: Previous connect attempt hasn't been completed yet
 * - ECONNABORTED: Previous connect attempt has failed
 * - ENODEV: Cannot establish connection with XLIO Ultra API or NVIDIA NIC
 *
 * @note This function returns immediately. Connection establishment is
 * indicated by the XLIO_SOCKET_EVENT_ESTABLISHED event. If a connection
 * failure occurs an XLIO_SOCKET_EVENT_ERROR event will be delivered.
 *
 * @see connect(2)
 */
int xlio_socket_connect(xlio_socket_t sock, const struct sockaddr *to, socklen_t tolen);
 
/**
 * @brief Listen for incoming connections
 *
 * Configures the socket to listen for incoming connections. Requires that
 * the polling group has a socket_accept_cb callback registered.
 *
 * @param sock The socket to configure for listening
 * @return 0 on success, -1 on error (errno is set)
 *
 * @par Error Codes:
 * - ENOTCONN: No accept callback registered in the polling group
 * - EINVAL: Socket is already connected
 * - EADDRINUSE: Another socket is already listening on the same port
 * - ENODEV: Trying to listen on a non-NVIDIA NIC or an internal error
 *           preventing the socket from being offloaded
 *
 * @note The socket must be bound before calling this function.
 *
 * @see listen(2)
 */
int xlio_socket_listen(xlio_socket_t sock);
 
/**
 * @brief Get InfiniBand protection domain
 *
 * Returns the InfiniBand protection domain associated with the socket.
 * This can be used for registering memory regions for zero-copy operations.
 *
 * @param sock The socket to query
 * @return Pointer to ibv_pd structure, or NULL on error
 *
 * @note Socket must be connected or in progress of connecting.
 */
struct ibv_pd *xlio_socket_get_pd(xlio_socket_t sock);
 
/**
 * @brief Detach socket from polling group
 *
 * Removes the socket from its current polling group. The socket becomes
 * inactive and will not generate events until attached to another group.
 *
 * @param sock The socket to detach
 * @return 0 on success, -1 on error
 *
 * @par Error Codes:
 * - EINVAL: Socket is not connected or already detached
 * - ENOTSUP: Not supported with listen sockets
 *
 * @note During the 2-step socket migration (detach -> attach), there is a time window
 * during which RX packets are dropped until the socket is completely attached to
 * the new group. Applications should minimize this window to avoid packet loss and
 * TCP retransmissions.
 */
int xlio_socket_detach_group(xlio_socket_t sock);
 
/**
 * @brief Attach socket to polling group
 *
 * Attaches a previously detached socket to a polling group. The socket
 * will begin generating events according to the group's configuration.
 *
 * @param sock The socket to attach
 * @param group The polling group to attach to
 * @return 0 on success, -1 on error
 *
 * @par Error Codes:
 * - EINVAL: Socket is already attached
 * - ENOMEM: No memory to complete the operation
 * - ENOTCONN: Failed to attach TX flow
 * - ECONNABORTED: Failed to attach RX flow
 */
int xlio_socket_attach_group(xlio_socket_t sock, xlio_poll_group_t group);
 
/** @} */ // end of xlio_socket group
 
/**
 * @defgroup xlio_tx Transmit Operations
 * @brief High-performance data transmission functions
 *
 * The XLIO Ultra API provides efficient transmission capabilities with
 * zero-copy support and flexible batching options.
 *
 * @section tx_properties TX Flow Properties
 * - Non-blocking operation
 * - No partial write support - accepts all data unless memory allocation fails
 * - Zero-copy completion callbacks for memory management
 * - Inline send operations support for small data
 * - Data aggregation with explicit flush control
 *
 * @section tx_limitations TX Flow Limitations
 * - Currently, data can be pushed to wire in the RX flow regardless of the flush logic
 * - Avoid using xlio_socket_flush() for a XLIO_GROUP_FLAG_DIRTY group
 * - For a XLIO_GROUP_FLAG_DIRTY group, usage of XLIO_SOCKET_SEND_FLAG_FLUSH is limited,
 *   it's better to avoid using them both simultaneously.
 *
 * @{
 */
 
/**
 * @brief Send data on a socket
 *
 * Sends data on the specified socket using zero-copy by default.
 * The operation is non-blocking and accepts all data unless memory allocation fails.
 *
 * @param sock The socket to send data on
 * @param data Pointer to the data to send
 * @param len Length of the data
 * @param attr Send attributes controlling the operation
 * @return 0 on success, -1 on error (errno is set)
 *
 * @par Error Codes:
 * - ENOMEM: Insufficient memory (recoverable by retrying later)
 * - Other errors are generally not recoverable
 *
 * @note For zero-copy operation, the memory must be registered with the
 * InfiniBand protection domain obtained from xlio_socket_get_pd().
 *
 * @see xlio_socket_send_attr
 */
int xlio_socket_send(xlio_socket_t sock, const void *data, size_t len,
                     const struct xlio_socket_send_attr *attr);
 
/**
 * @brief Send vectored data on a socket
 *
 * Sends data from multiple buffers (scatter-gather) on the specified socket.
 *
 * @param sock The socket to send data on
 * @param iov Array of iovec structures describing the data buffers
 * @param iovcnt Number of iovec structures
 * @param attr Send attributes controlling the operation
 * @return 0 on success, -1 on error (errno is set)
 *
 * @see xlio_socket_send()
 */
int xlio_socket_sendv(xlio_socket_t sock, const struct iovec *iov, unsigned iovcnt,
                      const struct xlio_socket_send_attr *attr);
 
/**
 * @brief Flush all dirty sockets in a polling group
 *
 * For polling groups created with XLIO_GROUP_FLAG_DIRTY, this function
 * flushes all sockets that have pending data to send. This provides
 * batch flushing capabilities for improved performance.
 *
 * @param group The polling group to flush
 *
 * @note This function should only be used with groups that have the
 * XLIO_GROUP_FLAG_DIRTY flag set.
 */
void xlio_poll_group_flush(xlio_poll_group_t group);
 
/**
 * @brief Flush pending data on a socket
 *
 * Forces transmission of any data queued on the socket. XLIO aggregates data
 * by default for efficiency and user logic simplification.
 *
 * This function doesn't guarantee immediate transmission, because TCP algorithms
 * and congestion/flow control may affect transmission.
 *
 * @param sock The socket to flush
 *
 * @note Avoid using this function with sockets in XLIO_GROUP_FLAG_DIRTY groups.
 * Use xlio_poll_group_flush() instead for better performance for such groups.
 */
void xlio_socket_flush(xlio_socket_t sock);
 
/** @} */ // end of xlio_tx group
 
/**
 * @defgroup xlio_rx Receive Operations
 * @brief Zero-copy receive buffer management
 *
 * The XLIO Ultra API provides zero-copy receive capabilities through
 * a buffer management system. Received data is delivered via callbacks
 * with buffer descriptors that must be returned to the system.
 *
 * xlio_buf structure contains an uninitialized userdata field which can be used
 * by the application to store any data during its ownership on the buffer.
 * For example, the field can be used to organize a list without a container
 * allocation, or to add a reference counter to the buffer.
 *
 * @section rx_data_alignment Data Alignment Considerations
 * XLIO Ultra API does not guarantee alignment for zero-copy RX data. The data
 * alignment depends on the underlying network headers and packet structure.
 *
 * @{
 */
 
/**
 * @brief Free a receive buffer (socket-specific)
 *
 * Returns a receive buffer to the system for reuse. This function should
 * be called for every buffer received via the RX callback.
 *
 * @param sock The socket that received the buffer
 * @param buf The buffer descriptor to free
 *
 * @note The buffer must not be accessed after calling this function.
 */
void xlio_socket_buf_free(xlio_socket_t sock, struct xlio_buf *buf);
 
/**
 * @brief Free a receive buffer (group-specific)
 *
 * Returns a receive buffer to the system for reuse. This function allows to
 * return a buffer outside of the original socket lifecycle.
 *
 * @param group The polling group
 * @param buf The buffer descriptor to free
 *
 * @note The buffer must not be accessed after calling this function.
 */
void xlio_poll_group_buf_free(xlio_poll_group_t group, struct xlio_buf *buf);
 
/** @} */ // end of xlio_rx group
 
/** @} */ // end of xlio_ultra_api group


XLIO Zerocopy API Data Structures
/**
 * @addtogroup xlio_ultra_api XLIO Ultra API
 * @{
 */
 
/**
 * @brief Polling group handle
 * @ingroup xlio_poll_group
 *
 * Opaque handle representing a polling group for event management.
 */
typedef uintptr_t xlio_poll_group_t;
 
/**
 * @brief Socket handle
 * @ingroup xlio_socket
 *
 * Opaque handle representing an XLIO high-performance socket.
 */
typedef uintptr_t xlio_socket_t;
 
/**
 * @addtogroup xlio_rx
 * @{
 */
 
/**
 * @brief Buffer descriptor
 *
 * Opaque structure representing a receive buffer in zero-copy RX operations.
 * Buffers are provided via RX callbacks and must be returned to XLIO.
 *
 * @par Buffer Lifecycle:
 * 1. Buffer provided to application via xlio_socket_rx_cb_t
 * 2. Application processes data and optionally uses userdata field
 * 3. Application returns buffer via xlio_socket_buf_free() or xlio_poll_group_buf_free()
 *
 * @par User Data Field:
 * - Available for application use during buffer ownership
 * - Can be used for reference counting, linking, or other purposes
 * - Not initialized by XLIO
 *
 * @par Structure Members:
 * - uint64_t userdata: User data field available during buffer ownership
 */
struct xlio_buf {
    uint64_t userdata;
};
 
/** @} */ // end of xlio_rx group
 
/**
 * @defgroup xlio_callbacks Event Callbacks
 * @brief Callback functions for handling socket events
 *
 * The XLIO Ultra API uses callbacks to notify applications of various
 * events including connection state changes, data arrival, and completion
 * of zero-copy operations.
 *
 * Most of the callbacks are expected from the xlio_poll_group_poll() context.
 *
 * @{
 */
 
/**
 * @brief Memory allocation callback function
 *
 * This callback is invoked when XLIO allocates memory regions that
 * can be used for RX buffers. Applications can use this information
 * for memory management or preparation.
 *
 * @param addr Base address of the allocated memory
 * @param len Size of the allocated memory
 * @param hugepage_size Page size if hugepages are used, 0 for regular pages
 *
 * @note If hugepage_size is non-zero, both addr and len are aligned to
 * the page size boundary. For external allocators, hugepage_size is
 * always reported as zero.
 *
 * @see xlio_init_attr
 */
typedef void (*xlio_memory_cb_t)(void *addr, size_t len, size_t hugepage_size);
 
/** @brief Socket events */
enum {
    /** TCP connection established. */
    XLIO_SOCKET_EVENT_ESTABLISHED = 1,
    /** Socket terminated and no further events are possible. */
    XLIO_SOCKET_EVENT_TERMINATED,
    /** Passive close. */
    XLIO_SOCKET_EVENT_CLOSED,
    /** An error occurred, see the error code value. */
    XLIO_SOCKET_EVENT_ERROR,
};
 
/**
 * @brief Socket event callback function
 *
 * This callback is invoked when socket state changes occur, such as
 * connection establishment, errors, or termination.
 *
 * @param sock The socket generating the event
 * @param userdata_sq User data associated with the socket
 * @param event The event type (XLIO_SOCKET_EVENT_*)
 * @param value Event-specific value (error code for ERROR events, 0 otherwise)
 *
 * @par Event Types:
 * - XLIO_SOCKET_EVENT_ESTABLISHED: TCP connection established
 * - XLIO_SOCKET_EVENT_TERMINATED: Socket terminated, no further events
 * - XLIO_SOCKET_EVENT_CLOSED: Passive close by remote peer
 * - XLIO_SOCKET_EVENT_ERROR: Error occurred, see value for error code
 *
 * @par Error Codes (for ERROR events):
 * - ECONNABORTED: Connection aborted by local side
 * - ECONNRESET: Connection reset by remote side
 * - ECONNREFUSED: Connection refused during handshake
 * - ETIMEDOUT: Connection timed out
 *
 * @note Send operations are allowed only from the ESTABLISHED event context.
 *
 * @see xlio_poll_group_attr
 */
typedef void (*xlio_socket_event_cb_t)(xlio_socket_t sock, uintptr_t userdata_sq, int event,
                                       int value);
 
/**
 * @brief Zero-copy completion callback function
 *
 * This callback is invoked when a zero-copy send operation completes,
 * allowing the application to reclaim or reuse the transmitted buffers.
 *
 * @param sock The socket that completed the operation
 * @param userdata_sq User data associated with the socket
 * @param userdata_op User data associated with the specific operation
 *
 * @par Calling Contexts:
 * - xlio_poll_group_poll() (most common)
 * - xlio_socket_send() (if data is immediately flushed)
 * - xlio_socket_flush() / xlio_poll_group_flush()
 *
 * @note Send operations are allowed in this callback unless the socket
 * is being destroyed.
 *
 * @see xlio_socket_send_attr
 * @see xlio_poll_group_attr
 */
typedef void (*xlio_socket_comp_cb_t)(xlio_socket_t sock, uintptr_t userdata_sq,
                                      uintptr_t userdata_op);
 
/**
 * @brief Receive data callback function
 *
 * This callback is invoked when TCP payload arrives on a socket.
 * Each call provides a single contiguous buffer containing received data.
 *
 * @param sock The socket that received the data
 * @param userdata_sq User data associated with the socket
 * @param data Pointer to the received data
 * @param len Length of the received data
 * @param buf Buffer descriptor that must be returned via xlio_*_buf_free()
 *
 * @note The data pointer is valid only until the buffer is freed.
 * The buffer's userdata field can be used during user ownership.
 *
 * @see xlio_socket_buf_free()
 * @see xlio_poll_group_buf_free()
 * @see xlio_poll_group_attr
 */
typedef void (*xlio_socket_rx_cb_t)(xlio_socket_t sock, uintptr_t userdata_sq, void *data,
                                    size_t len, struct xlio_buf *buf);
 
/**
 * @brief Accept callback function
 *
 * This callback is invoked when a new connection is accepted on a
 * listening socket. The new socket is automatically created and
 * associated with the same polling group.
 *
 * @param sock The newly accepted socket
 * @param parent The listening socket that accepted the connection
 * @param parent_userdata_sq User data from the parent socket
 *
 * @note The new socket inherits the polling group from the parent but
 * may need additional configuration (e.g., userdata_sq update).
 *
 * @see xlio_socket_update()
 * @see xlio_poll_group_attr
 */
typedef void (*xlio_socket_accept_cb_t)(xlio_socket_t sock, xlio_socket_t parent,
                                        uintptr_t parent_userdata_sq);
 
/** @} */ // end of xlio_callbacks group
 
/**
 * @addtogroup xlio_init
 * @{
 */
 
/**
 * @brief XLIO initialization attributes
 *
 * Structure containing parameters for XLIO initialization with xlio_init_ex().
 *
 * @par Memory Management:
 * - memory_cb: Called when XLIO allocates memory regions for RX buffers
 * - memory_alloc/memory_free: Optional external allocator functions
 *
 * @par External Allocator Notes:
 * - When external allocator is provided, XLIO uses it instead of internal allocation
 * - Current implementation allocates a single memory block during xlio_init_ex()
 * - For external allocators, hugepage_size in memory_cb is always reported as zero
 *
 * @par Structure Members:
 * - unsigned flags: Initialization flags (reserved for future use)
 * - xlio_memory_cb_t memory_cb: Memory allocation notification callback
 * - void *(*memory_alloc)(size_t): Optional external memory allocator function
 * - void (*memory_free)(void *): Optional external memory deallocator function
 */
struct xlio_init_attr {
    unsigned flags;
    xlio_memory_cb_t memory_cb;
 
    /* Optional external user allocator for XLIO buffers. */
    void *(*memory_alloc)(size_t);
    void (*memory_free)(void *);
};
 
/** @} */ // end of xlio_init group
 
/**
 * @addtogroup xlio_poll_group
 * @{
 */
 
/** Sockets and rings will be protected with locks regardless of XLIO configuration. */
#define XLIO_GROUP_FLAG_SAFE 0x1
/** Group will keep dirty sockets to be flushed with xlio_poll_group_flush(). */
#define XLIO_GROUP_FLAG_DIRTY 0x2
 
/**
 * @brief Polling group attributes
 *
 * Structure containing configuration for a polling group creation and updates.
 * Event callbacks are registered per group, allowing different handling logic
 * for different types of connections.
 *
 * @par Required Callbacks:
 * - socket_event_cb: Must be provided (handles connection state changes)
 *
 * @par Optional Callbacks:
 * - socket_comp_cb: Zero-copy completion notifications
 * - socket_rx_cb: Receive data notifications
 * - socket_accept_cb: New connection acceptance (required for listening sockets)
 *
 * @par Structure Members:
 * - unsigned flags: Group flags (XLIO_GROUP_FLAG_*)
 * - xlio_socket_event_cb_t socket_event_cb: Socket event callback (required)
 * - xlio_socket_comp_cb_t socket_comp_cb: Zero-copy completion callback (optional)
 * - xlio_socket_rx_cb_t socket_rx_cb: Receive data callback (optional)
 * - xlio_socket_accept_cb_t socket_accept_cb: Accept callback for listening sockets (optional)
 */
struct xlio_poll_group_attr {
    unsigned flags;
 
    xlio_socket_event_cb_t socket_event_cb;
    xlio_socket_comp_cb_t socket_comp_cb;
    xlio_socket_rx_cb_t socket_rx_cb;
    xlio_socket_accept_cb_t socket_accept_cb;
};
 
/** @} */ // end of xlio_poll_group group
 
/**
 * @addtogroup xlio_socket
 * @{
 */
 
/**
 * @brief Socket creation attributes
 *
 * Structure containing parameters for socket creation with xlio_socket_create().
 * The socket is automatically associated with the specified polling group.
 *
 * @par Domain Support:
 * - AF_INET: IPv4 support
 * - AF_INET6: IPv6 support
 *
 * @par User Data:
 * - userdata_sq: Application-defined value for socket identification in callbacks
 * - Can be updated later with xlio_socket_update()
 *
 * @par Structure Members:
 * - unsigned flags: Socket flags (reserved for future use)
 * - int domain: Address family (AF_INET or AF_INET6)
 * - xlio_poll_group_t group: Polling group to associate socket with
 * - uintptr_t userdata_sq: User data for socket identification in callbacks
 */
struct xlio_socket_attr {
    unsigned flags;
    int domain; /* AF_INET or AF_INET6 */
    xlio_poll_group_t group;
    uintptr_t userdata_sq;
};
 
/** @} */ // end of xlio_socket group
 
/**
 * @addtogroup xlio_tx
 * @{
 */
 
/** Flush socket after queueing the data. */
#define XLIO_SOCKET_SEND_FLAG_FLUSH 0x1
/** Copy user data to the internal buffers instead of taking ownership. */
#define XLIO_SOCKET_SEND_FLAG_INLINE 0x2
 
/**
 * @brief Send operation attributes
 *
 * Structure containing parameters for send operations (xlio_socket_send/sendv).
 * Controls zero-copy behavior, flushing, and completion tracking.
 *
 * @par Zero-Copy Operation:
 * - mkey: Memory key for registered memory regions
 * - userdata_op: User data provided to completion callback
 * - For zero-copy, memory must be registered with ibv_pd from xlio_socket_get_pd()
 *
 * @par Inline vs Zero-Copy:
 * - INLINE flag: Data copied to internal buffers, no completion callback
 * - Zero-copy: Data sent directly from user buffer, completion callback invoked
 *
 * @par Structure Members:
 * - unsigned flags: Send flags (XLIO_SOCKET_SEND_FLAG_*)
 * - uint32_t mkey: Memory key for zero-copy operation (ignored for inline)
 * - uintptr_t userdata_op: User data for completion callback (zero-copy only)
 */
struct xlio_socket_send_attr {
    unsigned flags;
    uint32_t mkey;
    uintptr_t userdata_op;
};
 
/** @} */ // end of xlio_tx group
 
/** @} */ // end of xlio_ultra_api group
