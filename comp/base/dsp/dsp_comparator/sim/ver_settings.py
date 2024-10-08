#!/usr/bin/env python3
SETTINGS = {
	"default" : {
		"DATA_WIDTH"   	 : "25"         	  ,
		"INPUT_REGS_EN"	 : "true"       	  ,
		"MODE" 	      	 : "\\\"><=\\\""	  ,
		"DSP_ENABLE"   	 : "true"       	  ,
		"DEVICE"     	 : "\\\"STRATIX10\\\"",
	},
	"input_regs_dis" : {
		"INPUT_REGS_EN" : "false"           ,
	},
	"high_data_width" : {
		"DATA_WIDTH"    : "128"             ,
	},
	"dsp_dis" : {
		"DSP_ENABLE"    : "false"           ,
	},
	"mode1" : {
		"MODE"          : "\\\">= \\\""     ,
	},
	"mode2" : {
		"MODE"          : "\\\"<= \\\""     ,
	},
	"device_ultrascale" : {
		"DEVICE"          : "\\\"ULTRASCALE\\\"",
	},

	"_combinations_" : (
	# Input registers, Data width      , DSP     , Mode  , Device
	(), # default setting
	("input_regs_dis",                                    				      ),
	(                 "high_data_width",                  				      ),
	("input_regs_dis","high_data_width",                  				      ),
	(		          "high_data_width","dsp_dis",        				      ),
	("input_regs_dis","high_data_width","dsp_dis",        				      ),
	(                                             "mode1",				      ),
	("input_regs_dis",                            "mode1",				      ),
	(                                   "dsp_dis","mode1",				      ),
	("input_regs_dis",                  "dsp_dis","mode1",				      ),
	(                                             "mode2",				      ),
	("input_regs_dis",                            "mode2",				      ),
	(                                   "dsp_dis","mode2",				      ),
	("input_regs_dis",                  "dsp_dis","mode2",				      ),
	("input_regs_dis",                                    "device_ultrascale",),
	(                 "high_data_width",                  "device_ultrascale",),
	("input_regs_dis","high_data_width",                  "device_ultrascale",),
	(		          "high_data_width","dsp_dis",        "device_ultrascale",),
	("input_regs_dis","high_data_width","dsp_dis",        "device_ultrascale",),
	(                                             "mode1","device_ultrascale",),
	("input_regs_dis",                            "mode1","device_ultrascale",),
	(                                   "dsp_dis","mode1","device_ultrascale",),
	("input_regs_dis",                  "dsp_dis","mode1","device_ultrascale",),
	(                                             "mode2","device_ultrascale",),
	("input_regs_dis",                            "mode2","device_ultrascale",),
	(                                   "dsp_dis","mode2","device_ultrascale",),
	("input_regs_dis",                  "dsp_dis","mode2","device_ultrascale",),
	),

}
