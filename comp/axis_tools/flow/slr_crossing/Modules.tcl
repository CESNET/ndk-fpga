# Modules.tcl: Components include script
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS [list "SLR_CROSSING" "$OFM_PATH/comp/base/misc/slr_crossing" "FULL"]

lappend MOD "$ENTITY_BASE/axis_slr_crossing.vhd"
