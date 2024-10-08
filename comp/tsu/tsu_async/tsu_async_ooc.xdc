# tsu_async_ooc.xdc: Local constraints for tsu_async (to be used in OOC mode)
# Copyright (C) 2016 CESNET
# Author: Jiri Matousek <matousek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# $Id$
#


create_clock -name in_clk  -period 5 [get_ports IN_CLK]
create_clock -name out_clk -period 8 [get_ports OUT_CLK]
