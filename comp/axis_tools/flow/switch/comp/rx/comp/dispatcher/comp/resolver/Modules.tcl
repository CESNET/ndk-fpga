# Modules.tcl: Components include script
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend COMPONENTS [ list "GEN_MUX_ONEHOT" "$OFM_PATH/comp/base/logic/mux" "FULL" ]

lappend MOD "$ENTITY_BASE/resolver.vhd"
