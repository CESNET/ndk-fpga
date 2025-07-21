#!/bin/sh

# install.sh: Install script for the Verible GitLab stage runner.
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
# SPDX-License-Identifier: BSD-3-Clause

wget -O verible.tar.gz "https://github.com/chipsalliance/verible/releases/download/v0.0-4011-g03c61290/verible-v0.0-4011-g03c61290-linux-static-x86_64.tar.gz"
tar -xzf verible.tar.gz
mv verible-v0.0-4011-g03c61290/bin/* /usr/bin/
