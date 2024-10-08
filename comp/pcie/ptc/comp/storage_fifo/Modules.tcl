# Modules.tcl: Components include script
# Copyright (C) 2018 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths

# Paths to components
set FIFOXM_BASE  "$OFM_PATH/comp/base/fifo/fifox_multi"
set AUX_SIG_BASE "$OFM_PATH/comp/mfb_tools/logic/auxiliary_signals"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/dma_bus_pack.vhd"

# Components
lappend COMPONENTS [ list "FIFOX_MULTI"       $FIFOXM_BASE  "FULL" ]
lappend COMPONENTS [ list "AUXILIARY_SIGNALS" $AUX_SIG_BASE "FULL" ]

# Source files for implemented component
lappend MOD "$ENTITY_BASE/ptc_storage_fifo.vhd"
