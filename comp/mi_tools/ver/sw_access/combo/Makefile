# Makefile:
# Copyright (C) 2015 CESNET
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#

PLATFORM=`uname`
CC=gcc
LL=ld
INCLUDE=/usr/local/fpga/Modeltech/include
LIBCOMMLBR_INCLUDE?=../../../../../../../../libcommlbr
LIBCOMBO_INCLUDE?=../../../../../../../../libcombo/libcombo
FLAGS=-std=gnu99 -c -g -fPIC
DLL_FLAGS=-shared
DLL_SUFFIX=so
QUOTE="

TARGET = combo
SRCS = \
	combosix.c \
	$(LIBCOMBO_INCLUDE)/ibuf.c \
	$(LIBCOMBO_INCLUDE)/obuf.c \
	$(LIBCOMBO_INCLUDE)/phy.c \
	$(LIBCOMBO_INCLUDE)/i2cms.c \
	$(LIBCOMBO_INCLUDE)/i2c.c \
	$(LIBCOMBO_INCLUDE)/mdio.c


OBJS = $(SRCS:%.c=%.o)

all: lib$(TARGET).$(DLL_SUFFIX)

clean:
	rm -fR *.o *.$(DLL_SUFFIX) $(LIBCOMBO_INCLUDE)/*.o

lib$(TARGET).$(DLL_SUFFIX): $(OBJS)
	$(LL) $(DLL_FLAGS) -o $@ $^

%.o: %.c
	$(CC) $(FLAGS) -I$(INCLUDE) -I$(LIBCOMMLBR_INCLUDE) $(SOURCES) $< -o $@
