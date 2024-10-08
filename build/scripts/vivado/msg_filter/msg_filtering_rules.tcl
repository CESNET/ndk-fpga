# msg_filtering_rules.tcl: lists of message IDs to be filtered out for more
#                          concise logs
# Copyright (C) 2014 CESNET
# Author: Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# $Id$
#


# Third level filter
# ##################
# The list UNINTERESTING contains ID of uninteresting Vivado messages which can
# be be filtered out to make a list of produced messages shorter while keeping
# all interesting messages.
# None of the message IDs contained in the UNINTERESTING list should also be in
# the MOST_INTERESTING list.
set UNINTERESTING [list \
   {Synth 8-3331} \
   {Common 17-455} \
   {Synth 8-3295} \
   {Synth 8-3332}
]


# Fourth level filter
# ###################
# The list MOST_INTERESTING contains ID of only the most interesting Vivado
# messages which report the biggest synthesis and/or implementation issues.
# Thus, these messages should never be filtered out. Usually, only the messages
# with ID specified within the MOST_INTERESTING list are kept and all other
# messages are filtered out.
# None of the message IDs contained in the MOST_INTERESTING list should also be
# in the UNINTERESTING list.
set MOST_INTERESTING [list \
   {Synth 8-295} \
   {Common 17-55} \
   {Synth 8-614} \
   {Vivado 12-180} \
   {Synth 8-327} \
   {Synth 8-326} \
   {Synth 8-295}
]
