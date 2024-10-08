# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Tomas Hak <xhakto01@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set CONVERTER_BASE "$OFM_PATH/comp/mi_tools/converters/mi2avmm"

set COMPONENTS [ list \
    [ list "MI2AVMM" $CONVERTER_BASE "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/mailbox_client.ip"
set MOD "$MOD $ENTITY_BASE/sdm_client.vhd"

set MOD "$MOD $ENTITY_BASE/DevTree.tcl"

