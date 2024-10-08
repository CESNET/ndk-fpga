# core_bootstrap.tcl: Initializes all parameters for a chosen design by sourcing necessary
# configuration files
# Copyright (C) 2022 CESNET, z. s. p. o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

set OUTPUT_NAME   $env(OUTPUT_NAME)
set OFM_PATH      $env(OFM_PATH)
set COMBO_BASE    $env(COMBO_BASE)
set FIRMWARE_BASE $env(FIRMWARE_BASE)
set CARD_BASE     $env(CARD_BASE)
set CORE_BASE     $env(CORE_BASE)

set CORE_CONF  $CORE_BASE/config/core_conf.tcl
set CORE_CONST $CORE_BASE/config/core_const.tcl
set CORE_FUNC  $CORE_BASE/config/core_func.tcl

set CARD_CONF  $CARD_BASE/config/card_conf.tcl
set CARD_CONST $CARD_BASE/config/card_const.tcl

set APP_CONF $env(APP_CONF)

source $OFM_PATH/build/VhdlPkgGen.tcl
source $OFM_PATH/build/Shared.tcl

VhdlPkgBegin

# Source CORE functions
source $CORE_FUNC

# Source CORE user configurable parameters
source $CORE_CONF

# Source card specific user configurable parameters
source $CARD_CONF

# Source application user configurable parameters
if {$APP_CONF ne ""} {
    source $APP_CONF
}

# Source card-specific default parameters
source $CARD_CONST

# Generating of the VHDL package
source $CORE_CONST
