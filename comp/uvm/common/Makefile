# Makefile:
# Copyright (C) 2022 CESNET
# Author(s): Radek Isa <isa@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

include ../../../build/paths.mk

libprog.so: prog.c
	gcc -std=c11 -fPIC -I$(MODELSIM_PATH)/include prog.c -o prog.o -c
	ld -shared -o libprog.so prog.o -lpthread
