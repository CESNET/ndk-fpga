# Modules.tcl: Local include tcl script
# Copyright (C) 2016 CESNET
# Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set PAR_4B     "$ENTITY_BASE/.."
set FIFO       "$OFM_PATH/comp/base/fifo/fifo"

set COMPONENTS [ list \
                  [ list "EXTRACT_4B"             $PAR_4B               "FULL" ] \
                  [ list "FIFO_STATUS"          $FIFO                "BEHAV" ] \
               ]

set PACKAGES "$PACKAGES $OFM_PATH/comp/base/pkg/math_pack.vhd"

set MOD "$MOD $ENTITY_BASE/extract_4B_ver_ent.vhd"
set MOD "$MOD $ENTITY_BASE/extract_4B_ver_arch.vhd"
