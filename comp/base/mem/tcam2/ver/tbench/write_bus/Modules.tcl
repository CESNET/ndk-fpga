# Modules.tcl: Local include tcl script
# Copyright (C) 2020 CESNET z. s. p. o.
# Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SV_COMMON_BASE "$OFM_PATH/comp/ver"

set COMPONENTS [list [list "SV_COMMON" $SV_COMMON_BASE "FULL"]]

set MOD "$MOD $ENTITY_BASE/sv_wb_pkg.sv"
