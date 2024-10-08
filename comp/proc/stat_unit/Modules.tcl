# Copyright (C) 2011 CESNET
# Author: Pavel Benacek <benacek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#

set COUNT_DSP_BASE "$OFM_PATH/comp/base/logic/count"

# Components
set COMPONENTS [ list \
   [ list "COUNT_DSP" $COUNT_DSP_BASE "FULL" ] \
]

set MOD "$MOD $ENTITY_BASE/stat_unit_ent.vhd"
set MOD "$MOD $ENTITY_BASE/stat_unit_arch.vhd"
