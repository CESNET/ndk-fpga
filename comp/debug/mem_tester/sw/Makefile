# Makefile: To compile program
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

NFB_CFLAGS      = $(LIBNFB_CFLAGS) -std=gnu11
NFB_LDFLAGS     = $(LIBNFB_LDFLAGS)
NFB_LDLIBS      = -lnfb -lfdt -lm

C_BASE 			= c_base

TARGET          = mem_tester
SRCS            = $(C_BASE)/mem_tester.c $(C_BASE)/common.c $(C_BASE)/core.c

CC = gcc
CFLAGS = -pedantic -Wall -Wextra

$(TARGET): $(SRCS)
	$(CC) $(NFB_CFLAGS) $(CFLAGS) $^ -o $@ $(NFB_LDLIBS)

.PHONY: clean
clean:
	rm $(TARGET)
