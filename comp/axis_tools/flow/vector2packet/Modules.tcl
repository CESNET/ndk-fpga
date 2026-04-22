# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Tomáš Neckař <xneckat00@stud.fit.vut.cz>

# Packages
lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"

# Components
lappend COMPONENTS [ list "GEN_MUX" "$OFM_PATH/comp/base/logic/mux" "FULL" ]

# Files
lappend MOD "$ENTITY_BASE/axis_vector2packet.vhd"
