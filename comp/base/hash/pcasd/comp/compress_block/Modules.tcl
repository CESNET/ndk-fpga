# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

# Component paths
set COMP_BASE "$ENTITY_BASE/comp"

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/hash_pack.vhd"

# Components
lappend COMPONENTS [list "PCASD_CA_ROUND"    "$COMP_BASE/ca_round"                                  "FULL"]
lappend COMPONENTS [list "PCASD_RD_ROUND"    "$COMP_BASE/rd_round"                                  "FULL"]
lappend COMPONENTS [list "SIP_COMPRESS_WORD" "$ENTITY_BASE/../../../siphash/comp/sip_compress_word" "FULL"]

# Files
lappend MOD "$ENTITY_BASE/compress_block.vhd"
