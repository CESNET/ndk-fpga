# Modules.tcl: Local include tcl script
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author: Vlastimil Kosar <kosar@dyna-nic.com>, 2025
#
# SPDX-License-Identifier: BSD-3-Clause

global SYNTH_FLAGS

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/type_pack.vhd"

set MOD "$MOD $ENTITY_BASE/versal_axi_switch.vhd"
