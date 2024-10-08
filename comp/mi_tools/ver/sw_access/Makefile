# Makefile:
# Copyright (C) 2015 CESNET
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

include ../../../../build/paths.mk

TARGET = dpi_sw_access
SOURCES = dpi_sw_access.c
PLATFORM=`uname`
CC=gcc
LL=ld
INCLUDE=$(MODELSIM_PATH)/include
FLAGS=-std=c99 -fvisibility=hidden -c -g -fPIC
DLL_FLAGS=-shared -fvisibility=hidden
DLL_SUFFIX=so
QUOTE="

all: lib$(TARGET).$(DLL_SUFFIX)

clean:
	rm -fR *.h *.o *.$(DLL_SUFFIX)

$(TARGET).h: $(TARGET).sv
	vlib work
	echo $(QUOTE)import $(TARGET)::*; module top; endmodule$(QUOTE) > top.sv
	vlog -sv $(TARGET).sv
	vlog -sv -dpiforceheader -dpiheader $(TARGET).h top.sv
	rm -fR top.sv work

lib$(TARGET).$(DLL_SUFFIX): $(TARGET).o
	$(LL) $(DLL_FLAGS) -o $@ $^ -fini dpiclear

$(TARGET).o: $(TARGET).h $(SOURCES)
	$(CC) $(FLAGS) -I$(INCLUDE) $(SOURCES) -o $(TARGET).o
