# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2018 CESNET
# Author: Pavel Benáček <benacek@cesnet.cz>
# Author: Jan Kučera <jan.kucera@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PKG_BASE "$COMP_BASE/base/pkg"

set COMPONENTS [list [list "VCOMP" $PKG_BASE "VCOMPONENTS"]]


set PACKAGES  "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES  "$PACKAGES $ENTITY_BASE/dp_bram_xilinx_func.vhd"

set MOD  "$MOD $ENTITY_BASE/dp_bram_xilinx_ent.vhd"
set MOD  "$MOD $ENTITY_BASE/dp_bram_xilinx_arch.vhd"
