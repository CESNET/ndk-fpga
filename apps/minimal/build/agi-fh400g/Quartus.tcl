# Quartus.tcl: Quartus tcl script to compile whole FPGA design
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#           Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: The purpose of this file is described in the Parameterization section of
# the NDK-CORE documentation.

# ----- Setting basic synthesis options ---------------------------------------
# NDK & user constants
source $env(CARD_BASE)/src/Quartus.inc.tcl

# Create only a Quartus project for further design flow driven from Quartus GUI
# "0" ... full design flow in command line
# "1" ... project composition only for further dedesign flow in GUI
set SYNTH_FLAGS(PROJ_ONLY) "0"

# Associative array which is propagated to APPLICATION_CORE, add other
# parameters if necessary.
set APP_ARCHGRP(APP_CORE_ENABLE) $APP_CORE_ENABLE

# Convert associative array to list
set APP_ARCHGRP_L [array get APP_ARCHGRP]

# ----- Add application core to main component list ---------------------------
lappend HIERARCHY(COMPONENTS) \
    [list "APPLICATION_CORE" "$OFM_PATH/apps/minimal/top" $APP_ARCHGRP_L]

# Call main function which handle targets
nb_main
