# synth_settings.py:  Synthesis settings
# Copyright (C) 2024 BrnoLogic, Ltd.
# Author(s): Radek Hajek <hajek@brnologic.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default" : { # The default setting of synthesis
        "DEVICE"             : "\\\"ULTRASCALE\\\"",
        "REGIONS"            : "1",
        "REGION_SIZE"        : "1",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
        "AXI_DATA_WIDTH"     : "64",
        "USE_IN_PIPE"        : "false",
        "USE_OUT_PIPE"       : "false",
        "USE_OPT_REG1"       : "0",
    },
    "mfb_1_1_8_8" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "1",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
        "AXI_DATA_WIDTH"     : "64",
    },
    "mfb_1_8_32_8" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "32",
        "ITEM_WIDTH"         : "8",
        "AXI_DATA_WIDTH"     : "2048",
    },
    "mfb_4_8_8_8" : {
        "REGIONS"            : "4",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
        "AXI_DATA_WIDTH"     : "2048",
    },
    "use_pipe" : {
        "USE_IN_PIPE"        : "true",
        "USE_OUT_PIPE"       : "true",
    },
    "vivado" : {
        "DEVICE" : "\\\"ULTRASCALE\\\"",
    },
    "quartus" : {
        "DEVICE" : "\\\"STRATIX10\\\"",
    },
    "_combinations_" : (
    ("mfb_1_1_8_8",),
    ("mfb_1_1_8_8","use_pipe",),
    ("mfb_1_8_32_8",),
    ("mfb_1_8_32_8","use_pipe",),
    ("mfb_4_8_8_8",),
    ("mfb_4_8_8_8","use_pipe",),
    ),

}
