# open_loop.xdc: Local constrains for ASYNC_OPEN_LOOP
# Copyright (C) 2014 CESNET
# Author: Jakub Cabal <jakubcabal@gmail.com>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# $Id$
#

set_false_path -to [get_cells signal_Q1_reg]

# Some other constraints are applied as attributes directly in VHDL code.
