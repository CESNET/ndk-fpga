# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

CXX = g++
CXXFLAGS = -Wall -std=c++17 -O3
SHELL := /bin/bash

all: libchaskey.a

test: test.cpp libchaskey.a
	$(CXX) $(CXXFLAGS) test.cpp -o $@ -L. -lchaskey

libchaskey.a: chaskey.o
	ar rcs $@ $^

chaskey.o: chaskey.cpp
	$(CXX) -c -fPIC $(CXXFLAGS) $^ -o $@

clean:
	rm -f chaskey.o libchaskey.a test
