# asfifo_bram_xilinx.tcl: Local timing constrains
# Copyright (C) 2016 CESNET
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#



set_false_path -through [get_nets reset_async]
