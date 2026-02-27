# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2018 CESNET
# Author: Pavel Benáček <benacek@cesnet.cz>
# Author: Jan Kučera <jan.kucera@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause



set PACKAGES  "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
set PACKAGES  "$PACKAGES $ENTITY_BASE/sdp_bram_xilinx_func.vhd"

lappend MOD [list "$ENTITY_BASE/sdp_bram_xilinx_ent.vhd" PSLFILE "$ENTITY_BASE/sdp_bram_xilinx.psl"]
lappend MOD "$ENTITY_BASE/sdp_bram_xilinx_arch.vhd"
