#!/usr/bin/python
from socket import *
import fcntl, os, sys
import time
from collections import deque

ARG_LEN = 5
argc = len(sys.argv)
if (argc < ARG_LEN):
    print "Needs ", x - 1, " arguments [family, bind-addr, bind-port, expected-src-addr]"
    exit

myFamily = AF_INET
myFamilyStr = sys.argv[1]
if (myFamilyStr == "inet6"):
    myFamily = AF_INET6

myHost = sys.argv[2]
myPort = int(sys.argv[3])
myExpectedAddr = sys.argv[4]
mySendTo = sys.argv[5]

addrinfo = getaddrinfo(myHost, myPort, myFamily, SOCK_DGRAM)
addrinfo_sendto = getaddrinfo(mySendTo, myPort, myFamily, SOCK_DGRAM)

sock = socket(myFamily, SOCK_DGRAM) # create a UDP socket
sock.setsockopt(SOL_SOCKET, SO_REUSEPORT, 1)
print "Binding to: ", addrinfo[0][4]
sock.bind(addrinfo[0][4])

print "Waiting in recvfrom ..."
bytes, src_addr = sock.recvfrom(16)
print "Received ", len(bytes), " bytes: ", bytes

print "Debug Received src_addr: ", src_addr
if (myExpectedAddr != src_addr[0]):
    print "Unexpected received src_addr: ", src_addr[0]

sock.sendto("greetings", addrinfo_sendto[0][4])

sock.close()


