# async_reset.sdc: Local Quartus constrains
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set_false_path -through [get_pins -compatibility_mode "*|clrn"]
