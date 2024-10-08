# Modules.tcl: Local include tcl script
# Copyright (C) 2015 CESNET
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SV_COMMON_BASE "$OFM_PATH/comp/ver"

set COMPONENTS [list [list "SV_COMMON" $SV_COMMON_BASE "FULL"]]

set MOD "$MOD $ENTITY_BASE/sv_wl_pkg.sv"
