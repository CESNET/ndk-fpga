# Modules.tcl: Components include script
# Copyright (C) 2021 CESNET
# Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Set paths
set SV_COMMON   "$OFM_PATH/comp/ver"
set SV_MVB	"$OFM_PATH/comp/mvb_tools/ver"
set COMPONENTS [list \
      [ list "SV_COMMON"   $SV_COMMON  "FULL"] \
      [ list "SV_MVB"	   $SV_MVB     "FULL"] \
]
