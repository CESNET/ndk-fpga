# Makefile:
# Copyright (C) 2015 CESNET
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
OFM_PATH = ../../../../../..
include $(OFM_PATH)/build/paths.mk

TARGET1 = paramsctl
TARGET2 = directctl
TARGET3 = comboctl
TARGET4 = nfbctl
PLATFORM=`uname`
CC=gcc
LL=ld
INCLUDE=$(MODELSIM_PATH)/include
COMBO_INCLUDE=../../combo
NFB_INCLUDE=../../nfb
LIBCOMMLBR_INCLUDE=../../../../../../../../../libcommlbr
FLAGS=-std=gnu99 -fvisibility=hidden -c -g -fPIC
DLL_FLAGS=-shared -fvisibility=hidden
DLL_SUFFIX=so
QUOTE="

all: lib$(TARGET1).$(DLL_SUFFIX) lib$(TARGET2).$(DLL_SUFFIX) lib$(TARGET3).$(DLL_SUFFIX) lib$(TARGET4).$(DLL_SUFFIX)

clean:
	rm -fR *.o *.$(DLL_SUFFIX)

lib$(TARGET1).$(DLL_SUFFIX): $(TARGET1).o
	$(LL) $(DLL_FLAGS) -o $@ $^ -init __dpiregisterself

$(TARGET1).o: $(TARGET1).c
	$(CC) $(FLAGS) -I$(INCLUDE) $(TARGET1).c -o $(TARGET1).o

lib$(TARGET2).$(DLL_SUFFIX): $(TARGET2).o
	$(LL) $(DLL_FLAGS) -o $@ $^ -init __dpiregisterself

$(TARGET2).o: $(TARGET2).c
	$(CC) $(FLAGS) -I$(INCLUDE) $(TARGET2).c -o $(TARGET2).o

lib$(TARGET3).$(DLL_SUFFIX): $(TARGET3).o
	$(LL) $(DLL_FLAGS) -o $@ $^ -init __dpiregisterself

$(TARGET3).o: $(TARGET3).c
	$(CC) $(FLAGS) -I$(INCLUDE) -I$(COMBO_INCLUDE) -I$(LIBCOMMLBR_INCLUDE) $(TARGET3).c -o $(TARGET3).o

lib$(TARGET4).$(DLL_SUFFIX): $(TARGET4).o
	$(LL) $(DLL_FLAGS) -o $@ $^ -init __dpiregisterself

$(TARGET4).o: $(TARGET4).c
	$(CC) $(FLAGS) -I$(INCLUDE) -I$(NFB_INCLUDE) $(TARGET4).c -o $(TARGET4).o
