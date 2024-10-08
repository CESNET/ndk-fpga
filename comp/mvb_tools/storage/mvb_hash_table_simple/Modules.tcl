# Modules.tcl: Components include script
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set SDP_MEMX    "$OFM_PATH/comp/base/mem/sdp_memx"

# Components
lappend COMPONENTS [ list "SDP_MEMX"  $SDP_MEMX  "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/mvb_hash_table_simple.vhd"
