# Modules.tcl: Components include script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Mario Kuka <kuka@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE "$OFM_PATH/comp/base/pkg"
set MUX_BASE "$OFM_PATH/comp/base/logic/mux"

set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
    [list "GEN_MUX" $MUX_BASE "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/dma_hdr_extractor.vhd"
