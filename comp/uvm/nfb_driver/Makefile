# Makefile:
# Copyright (C) 2022 CESNET
# Author(s): Radek Isa <isa@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

include ../../../build/paths.mk
PROTO_PATH=/usr/include/
PROTO_VER=nfb/ext/protobuf/v1/
PROTO_NAME=nfb

NFB_PROTO_EXISTS=$(shell [ -e $(PROTO_PATH)$(PROTO_VER)$(PROTO_NAME).proto ] && echo 1 || echo 0 )

ifeq ($(NFB_PROTO_EXISTS), 1)
CDEF=NFB_PROTO_API_V1
else
PROTO_PATH=
PROTO_VER=
PROTO_NAME=nfb_grpc
CDEF=NFB_PROTO_API_V0
endif

PROTO_FILE=$(PROTO_PATH)$(PROTO_VER)$(PROTO_NAME).proto

LIB=`pkg-config --libs protobuf grpc++ grpc` -lpthread -lfdt
PIC="-fpic"


libnfb_driver.so: nfb_driver.cc $(PROTO_NAME).pb.o $(PROTO_NAME).grpc.pb.o
	g++ ${PIC} -std=c++17 -pedantic -Wall -I$(MODELSIM_PATH)/include -I . -D $(CDEF) nfb_driver.cc -o nfb_driver.o -c
	g++ -shared -o libnfb_driver.so nfb_driver.o nfb.grpc.pb.o nfb.pb.o ${LIB} -lgrpc++_reflection
#	ld -shared -o libnfb_driver.so nfb_driver.o nfb_grpc.grpc.pb.o nfb_grpc.pb.o ${LIB} -lgrpc++_reflection

$(PROTO_NAME).pb.o: $(PROTO_FILE)
	protoc --cpp_out=. $(PROTO_VER)$(PROTO_NAME).proto
	g++ ${PIC} -fvisibility=hidden -std=c++17 -pedantic -Wall -I . $(PROTO_VER)$(PROTO_NAME).pb.cc -o nfb.pb.o -c

$(PROTO_NAME).grpc.pb.o: $(PROTO_PATH)$(PROTO_VER)$(PROTO_NAME).proto $(PROTO_NAME).pb.o
	protoc --grpc_out=. --plugin=protoc-gen-grpc=`which grpc_cpp_plugin` $(PROTO_VER)$(PROTO_NAME).proto
	g++ ${PIC} -fvisibility=hidden -std=c++17 -pedantic -Wall -I . $(PROTO_VER)$(PROTO_NAME).grpc.pb.cc -o nfb.grpc.pb.o -c

