# Vivado.tcl: Vivado tcl script to compile single module
# Copyright (C) 2016 CESNET
# Author: Jiri Matousek <matousek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#


# Globally defined variables
global env

# Basic path defined within Makefile
if { [info exists env(OFM_PATH)] } {
   set OFM_PATH $env(OFM_PATH)
} else {
   set OFM_PATH "../../../.."
}

# Source NetCOPE and aplication packages with constants, if they were defined
if { [info exists env(NETCOPE_CONST)] && ($env(NETCOPE_CONST) ne "") } {
   source $env(NETCOPE_CONST)
}
if { [info exists env(USER_CONST)] && ($env(USER_CONST) ne "") } {
   source $env(USER_CONST)
}

# Set auxiliary variables
set TOP_LEVEL_ENT "tsu_async"

# ----- Setting synthesis options ---------------------------------------------

# Basic options
set SYNTH_FLAGS(FPGA)              "xc7vh580thcg1931-2"
set SYNTH_FLAGS(MODULE)            $TOP_LEVEL_ENT
set SYNTH_FLAGS(OUTPUT)            $TOP_LEVEL_ENT
#set SYNTH_FLAGS(CONSTR)            ""
set SYNTH_FLAGS(OOC_MODE)          "1"
set SYNTH_FLAGS(PROJ_ONLY)         "0"

# Advanced options - may be used for tuning the synthesis
#set SYNTH_FLAGS(FANOUT_LIMIT)     "10000"
#set SYNTH_FLAGS(RESOURCE_SHARING) "auto"
set SYNTH_FLAGS(BUFG)             "36"
set SYNTH_FLAGS(NO_LUT_COMBINE)   "false"
#set SYNTH_FLAGS(SYNTH_DIRECTIVE)  "AreaOptimized_high"
set SYNTH_FLAGS(SOPT_DIRECTIVE)   "ExploreSequentialArea"

# ----- Defining module's hierarchy -------------------------------------------

# Hierarchy definition
# (it is required to reference the module as a component)
set HIERARCHY(PACKAGES)   ""
set HIERARCHY(MOD)        ""
set HIERARCHY(COMPONENTS) [list [list "tsu_async" ".." "SRC"]]


# ----- Synthesis of the module -----------------------------------------------

# Including synthesis procedures
source $OFM_PATH/build/Vivado.inc.tcl

# Manual sythtesis
SetupDesign SYNTH_FLAGS
AddInputFiles SYNTH_FLAGS HIERARCHY
SynthetizeDesign SYNTH_FLAGS

# Skip the rest if the synthesis was not run
if {[info exist SYNTH_FLAGS(PROJ_ONLY)]} {
   if {$SYNTH_FLAGS(PROJ_ONLY) == "1"} {
      PrintLabel "Save & Close"
      close_project
      return
   }
}

# Design optimization
PrintLabel "Additional Post-synthesis Optimization"
opt_design -directive ExploreArea -verbose

PrintLabel "Save & Close"

# Storing the results into a .dcp file
write_checkpoint -force ${TOP_LEVEL_ENT}.dcp

# Closing the project
close_project

