# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2003 CESNET
# Author: Martinek Tomas <martinek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components
set PACKAGES  "$OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/dp_bmem_ent.vhd"
set MOD "$MOD $ENTITY_BASE/sdp_bmem_ent.vhd"

lappend MOD [list "$ENTITY_BASE/dp_bmem_behav.vhd" VIVADO_SET_PROPERTY [list -quiet FILE_TYPE {VHDL}]]
lappend MOD [list "$ENTITY_BASE/sdp_bmem_behav.vhd" VIVADO_SET_PROPERTY [list -quiet FILE_TYPE {VHDL}]]

lappend SRCS(CONSTR_VIVADO) [list "$ENTITY_BASE/dp_bmem.tcl" SCOPED_TO_REF DP_BMEM PROCESSING_ORDER LATE]
