# Makefile:
# Copyright (C) 2016 CESNET
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
OFM_PATH = ../../..
include $(OFM_PATH)/build/paths.mk

TARGET = dpi_pcap
SOURCES = dpi_pcap.c
PLATFORM=`uname`
CC=gcc
LL=ld
INCLUDE=$(MODELSIM_PATH)/include
FLAGS=-std=gnu99 -c -g -fPIC
DLL_FLAGS=-shared
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
	$(LL) $(DLL_FLAGS) -o $@ $^ -lpcap

$(TARGET).o: $(TARGET).h $(SOURCES)
	$(CC) $(FLAGS) -I$(INCLUDE) $(SOURCES) -o $(TARGET).o
