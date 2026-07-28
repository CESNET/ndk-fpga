# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Martin Spinler <spinler@cesnet.cz>


SETTINGS = {
    "default" : { # Obligatory
        "INPUT_REGS"   : "true"             ,
        "DSP_ENABLE"   : "true"             ,
        "INPUT_WIDTH"  : "5"                ,
        "OUTPUT_WIDTH" : "10"               ,
        "DEVICE"       : "\\\"STRATIX10\\\"",
    },
    "input_regs_dis" : { # Disabling input registers
        "INPUT_REGS" : "false",
    },
    "dsp_dis" : { # Disabling DSP blocks to use logic for the counter
        "DSP_ENABLE" : "false",
    },
    "max_input_output_width" : { # Setting maximum widths of input and output
        "INPUT_WIDTH"  : "27",
        "OUTPUT_WIDTH" : "64",
    },
    "device_ultrascale" : { # Target device is UltraScale+
        "DEVICE" : "\\\"ULTRASCALE\\\"",
    },
    "device_agilex" : { # Target device is Agilex
        "DEVICE" : "\\\"AGILEX\\\"",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("input_regs_dis",                                                       ),
    (                 "dsp_dis",                                             ),
    ("input_regs_dis","dsp_dis",                                             ),
    (                           "max_input_output_width",                    ),
    ("input_regs_dis",          "max_input_output_width",                    ),
    (                 "dsp_dis","max_input_output_width",                    ),
    ("input_regs_dis","dsp_dis","max_input_output_width",                    ),
    (                                                    "device_ultrascale",),
    ("input_regs_dis",                                   "device_ultrascale",),
    (                 "dsp_dis",                         "device_ultrascale",),
    ("input_regs_dis","dsp_dis",                         "device_ultrascale",),
    (                           "max_input_output_width","device_ultrascale",),
    ("input_regs_dis",          "max_input_output_width","device_ultrascale",),
    (                 "dsp_dis","max_input_output_width","device_ultrascale",),
    ("input_regs_dis","dsp_dis","max_input_output_width","device_ultrascale",),
    (                                                    "device_agilex",   ),
    ("input_regs_dis",                                   "device_agilex",   ),
    (                 "dsp_dis",                         "device_agilex",   ),
    ("input_regs_dis","dsp_dis",                         "device_agilex",   ),
    (                           "max_input_output_width","device_agilex",   ),
    ("input_regs_dis",          "max_input_output_width","device_agilex",   ),
    (                 "dsp_dis","max_input_output_width","device_agilex",   ),
    ("input_regs_dis","dsp_dis","max_input_output_width","device_agilex",   ),
    ),
}
