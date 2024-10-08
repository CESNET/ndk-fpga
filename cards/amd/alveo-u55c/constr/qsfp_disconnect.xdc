# qsfp_disconnect.xdc
# Copyright (C) 2024 CESNET z.s.p.o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set_property IO_BUFFER_TYPE NONE [get_ports {QSFP0_TX_P[*]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP0_TX_N[*]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP1_TX_P[*]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP1_TX_N[*]}]
