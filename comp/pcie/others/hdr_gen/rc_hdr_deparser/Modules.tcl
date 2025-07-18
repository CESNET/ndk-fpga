# Modules.tcl: Components include script
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kriz <xkrizd01@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for implemented component

lappend PACKAGES "$COMP_BASE/base/pkg/math_pack.vhd"
lappend MOD "$ENTITY_BASE/rc_hdr_deparser.vhd"
