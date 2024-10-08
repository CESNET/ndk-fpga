# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set SDP_MEMX_BASE            "$OFM_PATH/comp/base/mem/sdp_memx"

# Components
set COMPONENTS [concat $COMPONENTS [list \
   [ list "SDP_MEMX"			$SDP_MEMX_BASE 			  "FULL"      ] \
]]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/multi_fifo.vhd"
