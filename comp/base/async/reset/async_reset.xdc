# async_reset.xdc: Local constrains for ASYNC_RESET
# Copyright (C) 2014 CESNET
# Author: Jakub Cabal <jakubcabal@gmail.com>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# $Id$
#

# This constrains will be applied everytime.
set_false_path -through [get_ports ASYNC_RST]
