# Modules.tcl: Modules.tcl script to include sources for h3hash.vhd
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

lappend PACKAGES  "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES  "$OFM_PATH/comp/base/pkg/type_pack.vhd"


lappend MOD "$ENTITY_BASE/h3_pack.vhd"
lappend MOD "$ENTITY_BASE/h3_core.vhd"
lappend MOD "$ENTITY_BASE/h3_hash.vhd"
