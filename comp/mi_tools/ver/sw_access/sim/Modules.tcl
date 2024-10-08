# Modules.tcl: Modules.tcl script to compile the design
# Copyright (C) 2015 CESNET
# Author: Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set SV_LIB "$SV_LIB $ENTITY_BASE/tools/paramsctl"
set SV_LIB "$SV_LIB $ENTITY_BASE/tools/directctl"
set SV_LIB "$SV_LIB $ENTITY_BASE/tools/comboctl"
set SV_LIB "$SV_LIB $ENTITY_BASE/tools/nfbctl"

set MOD "$MOD $ENTITY_BASE/dut.vhd"
set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
