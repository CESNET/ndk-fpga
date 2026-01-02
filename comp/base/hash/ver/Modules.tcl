# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

# Component paths
set COMP_BASE "$ENTITY_BASE/.."

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [list "SPOOKYHASH"  "$COMP_BASE/spookyhash"  "FULL"]
lappend COMPONENTS [list "SIPHASH"     "$COMP_BASE/siphash"     "FULL"]


# Files
lappend MOD "$ENTITY_BASE/hash_wrapper.vhd"
