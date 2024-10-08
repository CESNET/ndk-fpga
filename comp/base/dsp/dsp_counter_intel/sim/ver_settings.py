#!/usr/bin/env python3

SETTINGS = {
    "default" : { # Obligatory
        "INPUT_REGS"     : "true" ,
        "COUNT_DOWN"     : "false",
        "DSP_ENABLE"     : "true" ,
        "AUTO_RESET"     : "true" ,
        "COUNT_BY_WIDTH" : "5"    ,
        "RESULT_WIDTH"   : "10"   ,
    },
    "input_regs_dis" : { # Disabling input registers
        "INPUT_REGS" : "false",
    },
    "count_down" : { # Counting down
        "COUNT_DOWN" : "true",
    },
    "dsp_dis" : { # Disabling DSP blocks to use logic for the counter
        "DSP_ENABLE" : "false",
    },
    "no_auto_reset" : { # Forbiding the counter to overflow/underflow when it reaches its max/min value
        "AUTO_RESET" : "false",
    },
    "max_input_output_width" : { # Setting maximum widths of input and output
        "COUNT_BY_WIDTH" : "27",
        "RESULT_WIDTH"   : "64",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("input_regs_dis",                                                                ),
    (                 "count_down",                                                   ),
    ("input_regs_dis","count_down",                                                   ),
    (                              "dsp_dis",                                         ),
    ("input_regs_dis",             "dsp_dis",                                         ),
    (                 "count_down","dsp_dis",                                         ),
    ("input_regs_dis","count_down","dsp_dis",                                         ),
    (                                        "no_auto_reset",                         ),
    ("input_regs_dis",                       "no_auto_reset",                         ),
    (                 "count_down",          "no_auto_reset",                         ),
    ("input_regs_dis","count_down",          "no_auto_reset",                         ),
    (                              "dsp_dis","no_auto_reset",                         ),
    ("input_regs_dis",             "dsp_dis","no_auto_reset",                         ),
    (                 "count_down","dsp_dis","no_auto_reset",                         ),
    ("input_regs_dis","count_down","dsp_dis","no_auto_reset",                         ),
    (                                                        "max_input_output_width",),
    ("input_regs_dis",                                       "max_input_output_width",),
    (                 "count_down",                          "max_input_output_width",),
    ("input_regs_dis","count_down",                          "max_input_output_width",),
    (                              "dsp_dis",                "max_input_output_width",),
    ("input_regs_dis",             "dsp_dis",                "max_input_output_width",),
    (                 "count_down","dsp_dis",                "max_input_output_width",),
    ("input_regs_dis","count_down","dsp_dis",                "max_input_output_width",),
    (                                        "no_auto_reset","max_input_output_width",),
    ("input_regs_dis",                       "no_auto_reset","max_input_output_width",),
    (                 "count_down",          "no_auto_reset","max_input_output_width",),
    ("input_regs_dis","count_down",          "no_auto_reset","max_input_output_width",),
    (                              "dsp_dis","no_auto_reset","max_input_output_width",),
    ("input_regs_dis",             "dsp_dis","no_auto_reset","max_input_output_width",),
    (                 "count_down","dsp_dis","no_auto_reset","max_input_output_width",),
    ("input_regs_dis","count_down","dsp_dis","no_auto_reset","max_input_output_width",),
    ),
}
