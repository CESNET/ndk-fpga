# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

CXX = g++
CXXFLAGS = -Wall -std=c++17 -O3
SHELL := /bin/bash

all: libsiphash.a

pytest: test
	python3 -m venv test_venv
	source test_venv/bin/activate;               \
	pip install pytest;                          \
	pip install siphash-cffi;                    \
	pip install parse;                           \
	pytest;                                      \
	deactivate;                                  \
	rm -rf test_venv __pycache__ .pytest_cache;  \
	make clean

test: test.cpp libsiphash.a
	$(CXX) $(CXXFLAGS) test.cpp -o $@ -L. -lsiphash

libsiphash.a: siphash.o
	ar rcs $@ $^

siphash.o: siphash.cpp
	$(CXX) -c -fPIC $(CXXFLAGS) $^ -o $@

clean:
	rm -f siphash.o libsiphash.a test
