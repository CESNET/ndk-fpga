# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

# Component paths
set COMP_BASE "$ENTITY_BASE/.."

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

# Components
lappend COMPONENTS [list "SIPROUND"  "$COMP_BASE/sipround"  "FULL"]

# Files
lappend MOD "$ENTITY_BASE/sip_compress_word.vhd"
