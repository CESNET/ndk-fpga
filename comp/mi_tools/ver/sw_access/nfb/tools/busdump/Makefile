# Makefile:
# Copyright (C) 2018 CESNET
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#

TARGET = busdump
SRCS = ../../../../../../../../../../swbase/tools-debug/busdump/busdump.c
PLATFORM=`uname`
CC=gcc
LL=ld
INCLUDE=/usr/local/fpga/Modeltech/include
NFB_INCLUDE=../..
FLAGS=-std=gnu99 -fvisibility=hidden -c -g -fPIC -DDPI_VERIFICATION
DLL_FLAGS=-shared -fvisibility=hidden
DLL_SUFFIX=so
QUOTE="

OBJS = $(SRCS:%.c=%.o)

all: clean lib$(TARGET).$(DLL_SUFFIX)

clean:
	rm -fR $(OBJS) *.$(DLL_SUFFIX)

lib$(TARGET).$(DLL_SUFFIX): $(OBJS)
	$(LL) $(DLL_FLAGS) -o $@ $^ -init __dpiregisterself

%.o: %.c
	$(CC) $(FLAGS) -I$(INCLUDE) -I$(NFB_INCLUDE) $(SOURCES) $< -o $@
