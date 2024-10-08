# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2013 CESNET
# Author: Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set PKG_BASE            "$OFM_PATH/comp/base/pkg"

set MFB_FIFOX_BASE     "$OFM_PATH/comp/mfb_tools/storage/fifox"
set AUX_SIG_BASE       "$OFM_PATH/comp/mfb_tools/logic/auxiliary_signals"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/dma_bus_pack.vhd"

# list of sub-components
set COMPONENTS [ list \
   [ list "MFB_FIFOX"         $MFB_FIFOX_BASE  "FULL"] \
   [ list "AUXILIARY_SIGNALS" $AUX_SIG_BASE    "FULL"] \
]

# entity and architecture
set MOD "$MOD $ENTITY_BASE/dma2mfb.vhd"
