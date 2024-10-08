# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2015 CESNET
# Author: Pavel Benacek <benacek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Base directories

set DSP_MUX             "$OFM_PATH/comp/base/logic/mux_dsp"

# Packages
set PACKAGES            "$OFM_PATH/comp/base/pkg/math_pack.vhd"

# Componet lis
set COMPONENTS [list \
      [list "DSP_MULTIPLEXOR"    $DSP_MUX       "FULL" ]\
   ]

# Modules
set MOD "$MOD $ENTITY_BASE/flu_multiplexer_dsp.vhd"
