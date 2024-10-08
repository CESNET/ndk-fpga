# Modules.tcl: Components include script
# Copyright (C) 2016 CESNET z. s. p. o.
# Author(s): Lukas Kekely <kekely@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause


set COMPONENTS [list [ list "MUX" "$OFM_PATH/comp/base/logic/mux" "FULL"] ]

set MOD "$MOD $ENTITY_BASE/last_vld.vhd"
