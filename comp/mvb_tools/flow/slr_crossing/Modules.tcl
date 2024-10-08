# Modules.tcl: Components include script
# Copyright (C) 2019 CESNET z. s. p. o.
# Author: Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set COMPONENTS [list \
    [list "SLR_CROSSING"    "$OFM_PATH/comp/base/misc/slr_crossing"     "FULL"] \
]

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/mvb_slr_crossing.vhd"
