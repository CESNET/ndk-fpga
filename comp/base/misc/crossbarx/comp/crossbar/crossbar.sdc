# asfifo.xdc: Local constrains for ASFIFO
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# This constrains will be applied everytime.
set_multicycle_path -from [get_cells {sched_src_word_reg[*]}] -setup -start 1
set_multicycle_path -from [get_cells {sched_src_word_reg[*]}] -hold -start 1

