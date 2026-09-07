# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set FIFOXM_BASE    "$OFM_PATH/comp/base/fifo/fifox_multi"
set COMPACTOR_BASE "$OFM_PATH/comp/mfb_tools/flow/compactor"
set MFB_FIFOX_BASE "$OFM_PATH/comp/mfb_tools/storage/fifox"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [ list "DMA_PACKAGE"   "$OFM_PATH/comp/base/pkg" "DMA_PKG" ]
lappend COMPONENTS [ list "FIFOX_MULTI"   $FIFOXM_BASE    "FULL" ]
lappend COMPONENTS [ list "MFB_COMPACTOR" $COMPACTOR_BASE "FULL" ]
lappend COMPONENTS [ list "MFB_FIFOX"     $MFB_FIFOX_BASE "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/ptc_storage_fifo.vhd"
