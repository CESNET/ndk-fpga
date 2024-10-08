# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jan Kubalek <kubalek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set PKG_BASE            "$OFM_PATH/comp/base/pkg"

# Packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set AFIFOX_BASE       "$OFM_PATH/comp/base/fifo/asfifox"
set FIFOXM_BASE       "$OFM_PATH/comp/base/fifo/fifox_multi"
set HANDSH_BASE       "$OFM_PATH/comp/base/async/bus_handshake"
set ASFIFO_BASE       "$OFM_PATH/comp/base/fifo/asfifox"
set SHREG_BASE        "$OFM_PATH/comp/base/shreg/sh_reg_base"
set BRAM_BASE         "$OFM_PATH/comp/base/mem/sdp_bram"
set AUX_BASE          "$OFM_PATH/comp/mfb_tools/logic/auxiliary_signals"

set COMPONENTS [list \
    [ list "AFIFOX"            "$AFIFOX_BASE"                         "FULL" ] \
    [ list "FIFOXM"            "$FIFOXM_BASE"                         "FULL" ] \
    [ list "HANDSH"            "$HANDSH_BASE"                         "FULL" ] \
    [ list "ASFIFO"            "$ASFIFO_BASE"                         "FULL" ] \
    [ list "SHREG"             "$SHREG_BASE"                          "FULL" ] \
    [ list "BRAM"              "$BRAM_BASE"                           "FULL" ] \
    [ list "AUX"               "$AUX_BASE"                            "FULL" ] \
]

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/output_buffer.vhd"
