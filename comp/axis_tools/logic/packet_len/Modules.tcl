# Modules.tcl: Components include script
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): David Vodak <vodak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend MOD "$ENTITY_BASE/axis_packet_len.vhd"
