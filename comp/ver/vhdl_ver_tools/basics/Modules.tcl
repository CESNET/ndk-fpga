# Modules.tcl: Components include script
# Copyright (C) 2026 CESNET
# Author(s): Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


lappend COMPONENTS [ list "MATH_PACKAGE" "$OFM_PATH/comp/base/pkg" "MATH" ]
lappend COMPONENTS [ list "DMA_PACKAGE" "$OFM_PATH/comp/base/pkg" "DMA_PKG" ]

lappend MOD "$ENTITY_BASE/basics_test_pkg.vhd"
