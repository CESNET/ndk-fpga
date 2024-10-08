# datarst_drc.tcl: definition of procedure for reporting
#                  wide registers with resets in the design
# Copyright (C) 2014 CESNET
# Author: Jan Kucera <xkucer73@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# $Id$
#

# report wide registers with resets in the design
proc datarstCheck {} {
   # list to hold vios & wide regs with rst
   set vios {}
   set widerstregs {}
   # get wide buses & regs
   set widebuses [get_nets -hierarchical -filter {BUS_WIDTH > 8}]
   set wideregs [get_cells -of_objects $widebuses -filter {PRIMITIVE_SUBGROUP == flop}]
   # go through wide registers
   foreach widereg $wideregs {
      # get used RESET pins
      set rstpins [get_pins -of_objects $widereg -filter {REF_PIN_NAME == R && LOGIC_VALUE != zero} -quiet]
      if {[llength $rstpins] > 0} {
         # remove square brackets -> generics, arrays
         regsub -all {\[(\d*)\]} $widereg "" reglbl
         # search if exists
         if {[lsearch $widerstregs $reglbl] == -1} {
            lappend widerstregs $reglbl
            set file_name [get_property FILE_NAME $widereg]
            set line_number [get_property LINE_NUMBER $widereg]
            set msg "Wide register '$reglbl' with reset found \[$file_name:$line_number\]."
            set vio [ create_drc_violation -name {DATARST-1} -msg $msg ]
            lappend vios $vio
         }
      }
   }
   # return error code if something is found
   if {[llength $vios] > 0} {
      return -code error $vios
   } else {
      return {}
   }
}

# delete DRC, if exists
delete_drc_check -quiet {DATARST-1}

# define user DRC procedure
create_drc_check -name {DATARST-1} \
                 -desc {Report wide registers with reset in the design} \
                 -hiername {User Defined} \
                 -rule_body datarstCheck
