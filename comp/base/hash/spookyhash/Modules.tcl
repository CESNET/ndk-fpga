# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

# Component paths
set COMP_BASE "$ENTITY_BASE/comp"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [list "SPOOKY_SHORTEND"  "$COMP_BASE/shortend"  "FULL"]
lappend COMPONENTS [list "SPOOKY_REMAINDER" "$COMP_BASE/remainder" "FULL"]
lappend COMPONENTS [list "SPOOKY_SETS"      "$COMP_BASE/sets"      "FULL"]

# Files
lappend MOD "$ENTITY_BASE/spookyhash.vhd"
lappend MOD "$ENTITY_BASE/sv/spookyhash.sv"
