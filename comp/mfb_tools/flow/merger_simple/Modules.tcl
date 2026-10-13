# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET
# Author(s): Daniel Kondys <xkondy00@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set MFB_FIFOX_BASE "$OFM_PATH/comp/mfb_tools/storage/fifox"

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [ list "MFB_FIFOX" $MFB_FIFOX_BASE "FULL" ]

set MOD "$MOD $ENTITY_BASE/mfb_merger_simple.vhd"
set MOD "$MOD $ENTITY_BASE/mfb_merger_simple_gen.vhd"
