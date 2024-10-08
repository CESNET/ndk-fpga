# Makefile:
# Copyright (C) 2018 CESNET
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

include ../../../../../build/paths.mk

PLATFORM=`uname`
CC=gcc
LL=ld
INCLUDE=$(MODELSIM_PATH)/include
CFLAGS=-std=gnu99 -c -g -fPIC
DLL_FLAGS=-shared
DLL_SUFFIX=so
QUOTE="

TARGET = nfb
SRCS = \
	src/nfb.c


OBJS = $(SRCS:%.c=%.o)

all: lib$(TARGET).$(DLL_SUFFIX)

clean:
	rm -fR src/*.o *.$(DLL_SUFFIX)

lib$(TARGET).$(DLL_SUFFIX): $(OBJS)
	$(LL) $(DLL_FLAGS) -o $@ $^ -lfdt

%.o: %.c
	$(CC) $(CFLAGS) $(EXTRA_CFLAGS) -I$(INCLUDE) -I. $(SOURCES) $< -o $@
