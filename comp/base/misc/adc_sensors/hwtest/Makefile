# Makefile
# Copyright (C) 2019 CESNET
# Author(s): Lukas Hejcman <xhejcm01@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

CC=gcc
CFLAGS= -std=c99 -Wall -Wextra -Werror -g -pedantic
LDFLAGS= -lm
NAME=valcon
OUTPUTNAME=$(NAME).c

$ (NAME): $(OUTPUTNAME)
	$(CC) $(CFLAGS) $(OUTPUTNAME) -o $(NAME) $(LDFLAGS)

clean:
	$(RM) $(NAME) *.o core *.out

cleanall: clean
	$(RM) $(EXEC)

test:
	./test-all.sh
