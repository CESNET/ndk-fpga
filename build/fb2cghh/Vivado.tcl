# Vivado.tcl: Vivado tcl script to compile whole FPGA design
# Copyright (C) 2022 CESNET z.s.p.o.
# Author(s): David Beneš <benes.david2000@seznam.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# ----- Setting basic synthesis options ---------------------------------------
# NDK & user constants
source $env(CARD_BASE)/src/Vivado.inc.tcl

# Create only a Vivado project for further design flow driven from Vivado GUI
# "0" ... full design flow in command line
# "1" ... project composition only for further dedesign flow in GUI
set SYNTH_FLAGS(PROJ_ONLY) "0"

# ----- Add application core to main component list ---------------------------
lappend HIERARCHY(COMPONENTS) \
    [list "APPLICATION_CORE" "../../app/intel" "FULL"]

# Call main function which handle targets
nb_main
