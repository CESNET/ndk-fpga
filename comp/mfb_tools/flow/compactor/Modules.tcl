# Modules.tcl: Components include script
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set MFB_AUXILIARY_SIGNALS_BASE "$OFM_PATH/comp/mfb_tools/logic/auxiliary_signals"

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [list "MFB_AUXILIARY_SIGNALS" $MFB_AUXILIARY_SIGNALS_BASE "FULL"]

lappend MOD "$ENTITY_BASE/mfb_compactor.vhd"
