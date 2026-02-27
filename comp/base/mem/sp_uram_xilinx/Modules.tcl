# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2018 CESNET
# Author: Kamil Vojanec <xvojan00@stud.fit.vutbr.cz>
# SPDX-License-Identifier: BSD-3-Clause



#set PACKAGES  "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"
#set PACKAGES  "$PACKAGES $ENTITY_BASE/dp_uram_xilinx_func.vhd"

lappend MOD [list "$ENTITY_BASE/sp_uram_xilinx_ent.vhd" PSLFILE $ENTITY_BASE/sp_uram_xilinx.psl]
lappend MOD "$ENTITY_BASE/sp_uram_xilinx_arch.vhd"
