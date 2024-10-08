# open_loop.sdc: Local Quartus constrains for ASYNC_OPEN_LOOP
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set_false_path -to [get_registers {signal_Q1}]

# Some other constraints are applied as attributes directly in VHDL code.
