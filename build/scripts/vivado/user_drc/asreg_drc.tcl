# asreg_drc.tcl: definition of procedure for reporting
#                async reset regs in the design
# Copyright (C) 2014 CESNET
# Author: Jan Kucera <xkucer73@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# $Id$
#


# report asregs in the design
proc asregCheck {} {
   # lists to hold violations and cells
   set vios {}
   set synccells {}
   # get synchronous cells with async reg resets
   foreach cell [get_cells -of_objects [all_registers -async_pins] -filter {PRIMITIVE_SUBGROUP == flop} -quiet] {
      set parent [get_property parent $cell]
      if {[llength $parent] > 0 && [llength [get_clocks -of_objects $parent]] == 1} {
         lappend synccells $parent
      }
   }
   # remove duplicates
   set synccells [lsort -unique $synccells]
   # define the message
   set msg "Cell %ELG with only one clock domain uses registers with async reset."
   # create violation objects
   foreach cell $synccells {
      set file_name [get_property FILE_NAME $cell]
      set line_number [get_property LINE_NUMBER $cell]
      set msg "Cell %ELG with only one clock domain uses registers with async reset \[$file_name:$line_number\]."
      set vio [ create_drc_violation -name {ASREG-1} -msg $msg $cell ]
      lappend vios $vio
   }
   # return error code if something is found
   if {[llength $vios] > 0} {
      return -code error $vios
   } else {
      return {}
   }
}

# delete DRC, if exists
delete_drc_check -quiet {ASREG-1}

# define user DRC procedure
create_drc_check -name {ASREG-1} \
                 -desc {Report registers with async resets in the design in components with only one clock domain} \
                 -hiername {User Defined} \
                 -rule_body asregCheck
