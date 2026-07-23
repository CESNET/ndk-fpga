# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

# Component paths
set COMP_BASE "$ENTITY_BASE/comp"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/hash_pack.vhd"

# Components
lappend COMPONENTS [list "SIPROUND"           "$COMP_BASE/sipround"           "FULL"]
lappend COMPONENTS [list "SIP_COMPRESS_WORD"  "$COMP_BASE/sip_compress_word"  "FULL"]

# Files
lappend MOD "$ENTITY_BASE/siphash.vhd"
lappend MOD "$ENTITY_BASE/sv/siphash.sv"
