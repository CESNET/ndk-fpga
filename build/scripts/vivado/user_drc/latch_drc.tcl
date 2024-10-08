# latch_drc.tcl: definition of procedure for reporting LATCHes in the design
# Copyright (C) 2014 CESNET
# Author: Jan Kucera <xkucer73@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# $Id$
#


# report LATCHes in the design
proc latchCheck {} {
   # list to hold violations
   set vios {}
   # iterate through the objects to be checked
   foreach latch [get_cells * -hierarchical -filter {PRIMITIVE_SUBGROUP == latch} -quiet] {
      # define the message & file to report when violations are found
      set file_name [get_property FILE_NAME $latch]
      set line_number [get_property LINE_NUMBER $latch]
      set msg "Detected LATCH on cell %ELG \[$file_name:$line_number\]."
      set vio [ create_drc_violation -name {LATCH-1} -msg $msg $latch ]
      lappend vios $vio
   }
   if {[llength $vios] > 0} {
      return -code error $vios
   } else {
      return {}
   }
}

# delete DRC, if exists
delete_drc_check -quiet {LATCH-1}

# define user DRC procedure
create_drc_check -name {LATCH-1} \
                 -desc {Report LATCHes in the design} \
                 -hiername {User Defined} \
                 -rule_body latchCheck
