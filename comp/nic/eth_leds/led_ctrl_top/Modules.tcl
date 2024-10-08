# Modules.tcl: Script to compile single module
# Copyright (C) 2022 CESNET
# Author: Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set ASYNC_GENERAL_BASE "$OFM_PATH/comp/base/async/general"
set LED_CTRL_ADV_BASE  "$OFM_PATH/comp/nic/eth_leds/led_ctrl_adv"

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/type_pack.vhd"

lappend COMPONENTS [list "ASYNC_GENERAL" $ASYNC_GENERAL_BASE "FULL" ]
lappend COMPONENTS [list "LED_CTRL_ADV"  $LED_CTRL_ADV_BASE  "FULL" ]

lappend MOD "$ENTITY_BASE/led_ctrl_top.vhd"
