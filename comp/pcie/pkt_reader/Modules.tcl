# Modules.tcl: Modules of the component
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
# SPDX-License-Identifier: BSD-3-Clause


# Set paths
set PKG_BASE            "$OFM_PATH/comp/base/pkg"
set LOGIC_BASE          "$OFM_PATH/comp/base/logic"
set FIFO_BASE           "$OFM_PATH/comp/base/fifo"
set MEM_BASE            "$OFM_PATH/comp/base/mem"
set MISC_BASE           "$OFM_PATH/comp/base/misc"
set MFB_FIFOX_BASE      "$OFM_PATH/comp/mfb_tools/storage/fifox"
set MFB_AXI_BASE        "$OFM_PATH/comp/mfb_tools/axi"
set MFB_LOGIC_BASE      "$OFM_PATH/comp/mfb_tools/logic"

# Packages
lappend PACKAGES "$PKG_BASE/math_pack.vhd"
lappend PACKAGES "$PKG_BASE/type_pack.vhd"
lappend PACKAGES "$PKG_BASE/dma_bus_pack.vhd"

# Components
lappend COMPONENTS [ list "PPR_REQUEST_PROCESSOR"    "$ENTITY_BASE/comp/request_processor"  "FULL"       ]
lappend COMPONENTS [ list "N_LOOP_OP"                "$LOGIC_BASE/n_loop_op"                "FULL"       ]
lappend COMPONENTS [ list "FIFOX_MULTI"              "$FIFO_BASE/fifox_multi"               "FULL"       ]
lappend COMPONENTS [ list "MFB_FIFOX"                $MFB_FIFOX_BASE                        "FULL"       ]
lappend COMPONENTS [ list "MFB2AXI"                  "$MFB_AXI_BASE/mfb2axi"                "BEHAVIORAL" ]
lappend COMPONENTS [ list "AXI2MFB"                  "$MFB_AXI_BASE/axi2mfb"                "BEHAVIORAL" ]
lappend COMPONENTS [ list "BARREL_SHIFTER_GEN_PIPED" "$LOGIC_BASE/barrel_shifter"           "FULL"       ]
lappend COMPONENTS [ list "SDP_MEMX"                 "$MEM_BASE/sdp_memx"                   "BEHAVIORAL" ]
lappend COMPONENTS [ list "TRANS_SORTER"             "$MISC_BASE/trans_sorter"              "FULL"       ]

# Modules
lappend MOD "$ENTITY_BASE/pcie_pkt_reader.vhd"
