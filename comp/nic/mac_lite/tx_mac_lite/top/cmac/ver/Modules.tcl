# Modules.tcl: Components include script
# Copyright (C) 2017 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE           "$OFM_PATH/comp/base/pkg"
set MFB2LBUS_BASE      "$COMP_BASE/nic/cmac/cmac_wrapper/comp/mfb2lbus"
set SV_BASE            "$OFM_PATH/comp/ver"
set SV_LBUS_BASE       "$COMP_BASE/nic/cmac/ver"
set SV_FLU_BASE        "$OFM_PATH/comp/flu_tools/ver"
set SV_MI32_TOOLS_BASE "$OFM_PATH/comp/mi_tools/ver"

set PACKAGES           "$PACKAGES $PKG_BASE/math_pack.vhd"
set PACKAGES           "$PACKAGES $PKG_BASE/type_pack.vhd"

set COMPONENTS [list \
   [ list "MFB2LBUS" $MFB2LBUS_BASE      "FULL"] \
   [ list "SV_BASE"  $SV_BASE            "FULL"] \
   [ list "SV_LBUS"  $SV_LBUS_BASE       "FULL"] \
   [ list "SV_FLU"   $SV_FLU_BASE        "FULL"] \
   [ list "SV_MI32"  $SV_MI32_TOOLS_BASE "FULL"] \
]

set MOD "$MOD $ENTITY_BASE/tbench/dut_wrapper.vhd"
set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
