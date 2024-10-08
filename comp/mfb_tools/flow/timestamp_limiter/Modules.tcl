# Modules.tcl: Components include script
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Paths to components
set MFB_FLOW_BASE    "$OFM_PATH/comp/mfb_tools/flow"
set MFB_FIFOX_BASE   "$OFM_PATH/comp/mfb_tools/storage/fifox"
set BASE_LOGIC_BASE  "$OFM_PATH/comp/base/logic"
set MGMT_BASE        "$OFM_PATH/comp/nic/eth_phy/comp/mgmt"
set DSP_COUNTER_BASE "$OFM_PATH/comp/base/dsp/dsp_counter"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "MFB_PACKET_DELAYER"    "$MFB_FLOW_BASE/packet_delayer"    "FULL" ]
lappend COMPONENTS [ list "MFB_MERGER_GEN"        "$MFB_FLOW_BASE/merger_simple"     "FULL" ]
lappend COMPONENTS [ list "MFB_SPLITTER_GEN"      "$MFB_FLOW_BASE/splitter_simple"   "FULL" ]
lappend COMPONENTS [ list "MFB_FIFOX"             $MFB_FIFOX_BASE                    "FULL" ]
lappend COMPONENTS [ list "EDGE_DETECT"           "$BASE_LOGIC_BASE/edge_detect"     "FULL" ]
lappend COMPONENTS [ list "PULSE_EXTEND"          $MGMT_BASE                         "FULL" ]
lappend COMPONENTS [ list "DSP_COUNTER"           $DSP_COUNTER_BASE                  "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/mfb_timestamp_limiter.vhd"
lappend MOD "$ENTITY_BASE/DevTree.tcl"

