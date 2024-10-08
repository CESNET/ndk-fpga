# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET
# Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SV_COMMON_BASE "$OFM_PATH/comp/ver"

set COMPONENTS [list [list "SV_COMMON" $SV_COMMON_BASE "FULL"]]

set MOD "$MOD $ENTITY_BASE/sv_mi_common_pkg.sv"
