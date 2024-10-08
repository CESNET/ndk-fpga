# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2003 CESNET
# Author: Martinek Tomas <martinek@liberouter.org>
#
# SPDX-License-Identifier: BSD-3-Clause

# Source files for all components
set DECODER_BASE    "$OFM_PATH/comp/base/logic/dec1fn"
set EDETECT_BASE    "$OFM_PATH/comp/base/logic/edge_detect"

set COMPONENTS [list \
                  [ list "DECODER"     $DECODER_BASE    "FULL"] \
                  [ list "EDGE_DETECT" $EDETECT_BASE    "FULL"] \
               ]

set MOD "$MOD $ENTITY_BASE/interrupt_manager.vhd"
