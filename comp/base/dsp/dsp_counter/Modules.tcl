# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set XILINX_CNT_BASE "$OFM_PATH/comp/base/logic/count"
set INTEL_CNT_BASE  "$OFM_PATH/comp/base/dsp/dsp_counter_intel"

set COMPONENTS [list \
[list "DSP_COUNTER_INTEL" $INTEL_CNT_BASE  "FULL" ] \
[list "COUNT_DSP"         $XILINX_CNT_BASE "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/dsp_counter.vhd"
