# Vivado.tcl: Modules helper for including fpga_common core for specific card
# Copyright (C) 2026 CESNET z.s.p.o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
set OFM_PATH $env(OFM_PATH)

set ::env(APP_CONF) $OFM_PATH/apps/minimal/build/fb2cghh/app_conf.tcl
set ::env(CARD_BASE) $OFM_PATH/cards/silicom/fb2cghh

set ::env(ETH_PORTS) 2
set ::env(ETH_PORT_SPEED) 100
set ::env(ETH_PORT_CHAN) 1
set ::env(DMA_TYPE) 3
set ::env(NET_MOD_ENABLE) true

set ::env(APP_CORE_ENABLE) true
set ::env(BMC_ENABLE) false
set ::env(DMA_DEBUG_ENABLE) false
set ::env(CORE_BASE) $OFM_PATH/core/
set ::env(COMBO_BASE) $OFM_PATH/

source $env(CARD_BASE)/src/Vivado.inc.tcl

set APP_ARCHGRP(APP_CORE_ENABLE) $APP_CORE_ENABLE
set APP_ARCHGRP_L [array get APP_ARCHGRP]

lappend HIERARCHY(COMPONENTS) \
    [list "APPLICATION_CORE" "$OFM_PATH/apps/minimal/top" $APP_ARCHGRP_L] \
    [list "ALL_ENTITIES" "$OFM_PATH/tests/all_modules" "FULL"]

nb_main
