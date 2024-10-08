# open_loop_smd.sdc: Local Quartus constrains for ASYNC_OPEN_LOOP_SMD
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Relax setup and hold calculation
set_max_delay -from [get_registers "input_reg\[*\]"] -to [get_registers "sync1_reg\[*\]"] 100
set_min_delay -from [get_registers "input_reg\[*\]"] -to [get_registers "sync1_reg\[*\]"] -100

# Control skew for bits
set_max_skew -from [get_registers "input_reg\[*\]"] -to [get_registers "sync1_reg\[*\]"] -get_skew_value_from_clock_period src_clock_period -skew_value_multiplier 0.8

# Path delay (exception for net delay)
set_net_delay -max -from [get_registers "input_reg\[*\]"] -to [get_registers "sync1_reg\[*\]"] -get_value_from_clock_period dst_clock_period -value_multiplier 0.8
