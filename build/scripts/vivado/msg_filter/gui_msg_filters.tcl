# gui_msg_filters.tcl: definition of procedures for filtering Vivado messages
#                      in GUI (according to UNITERESTING and MOST_INTERESTING
#                      lists of message IDs)
# Copyright (C) 2014 CESNET
# Author: Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# $Id$
#


# define OFM_PATH variable
set OFM_PATH ../../../..


# load procedures defined in build/Vivado.inc.tcl
source $OFM_PATH/build/Vivado.inc.tcl


# -----------------------------------------------------------------------------
# filter_uninteresting_msg
# This procedure sets message suppression rules in such a way that all messages
# with IDs defined in the UNINTERESTING list are filtered out. All INFO
# messages are suppressed as well.
#
proc filter_uninteresting_msg { } {

   global OFM_PATH

   # import UNINTERESTING and MOST_INTERESTING lists
   source $OFM_PATH/build/scripts/vivado/msg_filter/msg_filtering_rules.tcl

   # suppress all INFO messages
   set_msg_config -severity {INFO} -suppress

   # suppress warning about resetting non-existing rules
   set_msg_config -id {Common 17-455} -suppress
   # reset suppression of WARNINGs, CRITICAL WARNINGs and ERRORs
   reset_msg_config -severity {WARNING} -suppress
   reset_msg_config -severity {CRITICAL WARNING} -suppress
   reset_msg_config -severity {ERROR} -suppress

   # suppress all messages with ID defined in the UNINTERESTING list
   foreach ID $UNINTERESTING {
      set_msg_config -id $ID -suppress
   }
}


# -----------------------------------------------------------------------------
# show_most_interesting_msg
# This procedure filters out all messages except those with ID contained in the
# MOST_INTERESTING list. INFO messages are always filtered out.
# This procedure usually take quite a long time (minutes) to finish!
proc show_most_interesting_msg { } {

   global OFM_PATH

   # import UNINTERESTING and MOST_INTERESTING lists
   source $OFM_PATH/build/scripts/vivado/msg_filter/msg_filtering_rules.tcl

   # suppress all INFO messages
   set_msg_config -severity {INFO} -suppress

   # suppress warning about resetting non-existing rules
   set_msg_config -id {Common 17-455} -suppress
   # reset suppression of WARNINGs, CRITICAL WARNINGs and ERRORs
   reset_msg_config -severity {WARNING} -suppress
   reset_msg_config -severity {CRITICAL WARNING} -suppress
   reset_msg_config -severity {ERROR} -suppress

   # store list of all log files into LOGFILES variable
   set LOGFILES [get_all_log_files]

   # parse all log files to get a list of IDs of all messages in these files
   set IDS [list ]
   foreach FILE $LOGFILES {
      set MSG_LINES [get_all_msg_lines $FILE]
      set IDS [concat $IDS [get_all_msg_ids $MSG_LINES]]
   }

   # filter out duplicit IDs from the list
   set IDS_UNIQUE [lsort -unique $IDS]

   # filter out all IDs contained in the MOST_INTERESTING list to get a list of
   # all messages to be suppressed
   foreach ID $MOST_INTERESTING {
      set POS [lsearch $IDS_UNIQUE $ID]
      if { $POS >= 0 } {
         set IDS_UNIQUE [lreplace $IDS_UNIQUE $POS $POS]
      }
   }

   # suppress all messages from the resulting list
   foreach ID $IDS_UNIQUE {
      set_msg_config -id $ID -suppress
   }
}


##### Auxilixary procedures ###################################################


# get_all_msg_ids
# This procedure returns a unique list of all message IDs from the list of
# given massage lines.
#
proc get_all_msg_ids { MSG_LINES } {

   # extract all message IDs into the IDS list
   set IDS [list ]
   foreach LINE $MSG_LINES {
      if { [regexp "\[A-Z\]\[a-z\]* \[0-9\]*-\[0-9\]*" $LINE ID] } {
         lappend IDS $ID
      }
   }

   # return a list of unique IDs
   return [lsort -unique $IDS]
}
