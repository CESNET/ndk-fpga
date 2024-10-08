# Modules.tcl: Local include script
# Copyright (C) 2016 CESNET z. s. p. o.
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set SV_COMMON_BASE "$OFM_PATH/comp/ver"

set COMPONENTS [list [list "SV_COMMON" $SV_COMMON_BASE "FULL"]]

set MOD "$MOD $ENTITY_BASE/sv_mfb_pkg.sv"
