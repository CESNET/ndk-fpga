# Modules.tcl: Local include tcl script
# Copyright (C) 2014 CESNET
# Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

#set PKG_BASE2 "$COMP_BASE/base/pkg"
#
#set COMPONENTS [list [list "VCOMP" $PKG_BASE2 "VCOMPONENTS"]]

set MOD "$MOD $ENTITY_BASE/dsp_pipe_3x48.vhd"
set MOD "$MOD $ENTITY_BASE/dsp_pipe_3x.vhd"
set MOD "$MOD $ENTITY_BASE/pipe_dsp_ent.vhd"
set MOD "$MOD $ENTITY_BASE/pipe_dsp.vhd"
