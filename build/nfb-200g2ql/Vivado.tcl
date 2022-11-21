# Vivado.tcl: Vivado tcl script to compile whole FPGA design
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kriz <danielkriz@cesnet.cz>
#

# NOTE: The purpose of this file is described in the Parametrization section of
# the NDK-CORE documentation.

# ----- Setting basic synthesis options ---------------------------------------
# NDK & user constants
source $env(CARD_BASE)/src/Vivado.inc.tcl

# Create only a Quartus project for further design flow driven from Quartus GUI
# "0" ... full design flow in command line
# "1" ... project composition only for further dedesign flow in GUI
set SYNTH_FLAGS(PROJ_ONLY) "0"

# Initialization of associative array to which user parameters should be added.
array set APP_ARCHGRP {}

# Convert associative array to list
set APP_ARCHGRP_L [array get APP_ARCHGRP]

# ----- Add application core to main component list ---------------------------
lappend HIERARCHY(COMPONENTS) \
    [list "APPLICATION_CORE" "../../app/intel" $APP_ARCHGRP_L]

# Call main function which handle targets
nb_main
