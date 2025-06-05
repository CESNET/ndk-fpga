# qsfp.xdc
# Copyright (C) 2025 CESNET z.s.p.o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# QSFP port 0 ----------------------------------------------------
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP0_TX_P[0]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP0_TX_N[0]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP0_TX_P[1]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP0_TX_N[1]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP0_TX_P[2]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP0_TX_N[2]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP0_TX_P[3]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP0_TX_N[3]}]

# QSFP port 1 ----------------------------------------------------
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP1_TX_P[0]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP1_TX_N[0]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP1_TX_P[1]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP1_TX_N[1]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP1_TX_P[2]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP1_TX_N[2]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP1_TX_P[3]}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP1_TX_N[3]}]

set_property IO_BUFFER_TYPE NONE [get_ports {QSFP*_RESET_N}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP*_LPMODE}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP*_SCL}]
set_property IO_BUFFER_TYPE NONE [get_ports {QSFP*_SDA}]
