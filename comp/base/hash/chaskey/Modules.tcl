# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

# Component paths
set COMP_BASE "$ENTITY_BASE/comp"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [list "CHASKEY_ROUND"          "$COMP_BASE/round"          "FULL"]
lappend COMPONENTS [list "CHASKEY_PROCESS_BLOCK"  "$COMP_BASE/process_block"  "FULL"]
lappend COMPONENTS [list "CHASKEY_REMAINDER"      "$COMP_BASE/remainder"      "FULL"]

# Files
lappend MOD "$ENTITY_BASE/chaskey.vhd"
lappend MOD "$ENTITY_BASE/sv/chaskey.sv"
