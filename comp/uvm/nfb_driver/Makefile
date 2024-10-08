# Makefile:
# Copyright (C) 2022 CESNET
# Author(s): Radek Isa <isa@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

include ../../../build/paths.mk

LIB=`pkg-config --libs protobuf grpc++ grpc` -lpthread -lfdt
PIC="-fpic"

libnfb_driver.so: nfb_driver.cc nfb_grpc.pb.o nfb_grpc.grpc.pb.o
	g++ ${PIC} -std=c++17 -pedantic -Wall -I$(MODELSIM_PATH)/include nfb_driver.cc -o nfb_driver.o -c
	g++ -shared -o libnfb_driver.so nfb_driver.o nfb_grpc.grpc.pb.o nfb_grpc.pb.o ${LIB} -lgrpc++_reflection
#	ld -shared -o libnfb_driver.so nfb_driver.o nfb_grpc.grpc.pb.o nfb_grpc.pb.o ${LIB} -lgrpc++_reflection

nfb_grpc.pb.o : nfb_grpc.proto
	protoc --cpp_out=. nfb_grpc.proto
	g++ ${PIC} -fvisibility=hidden -std=c++17 -pedantic -Wall nfb_grpc.pb.cc -o nfb_grpc.pb.o -c

nfb_grpc.grpc.pb.o : nfb_grpc.proto nfb_grpc.pb.o
	protoc --grpc_out=. --plugin=protoc-gen-grpc=`which grpc_cpp_plugin` nfb_grpc.proto
	g++ ${PIC} -fvisibility=hidden -std=c++17 -pedantic -Wall nfb_grpc.grpc.pb.cc -o nfb_grpc.grpc.pb.o -c

