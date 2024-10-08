# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2006 CESNET
# Author: Martin Kosek <kosek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# List of packages
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/first_one_detector.vhd"

set GEN_ENC_BASE  "$OFM_PATH/comp/base/logic/enc"

set COMPONENTS [list \
			[list "GEN_ENC" $GEN_ENC_BASE "FULL"]
		]
