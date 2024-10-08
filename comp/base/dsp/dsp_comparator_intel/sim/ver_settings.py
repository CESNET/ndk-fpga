#!/usr/bin/env python3
SETTINGS = {
	"default" : {
		"INPUT_REGS_EN"	 : "true"       	  ,
		"DATA_WIDTH"   	 : "25"         	  ,
		"DSP_ENABLE"   	 : "true"       	  ,
		"MODE" 	      	 : "\\\"><=\\\""	  ,
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
	"device_agilex" : {
		"DEVICE"          : "\\\"AGILEX\\\"",
	},

	"_combinations_" : (
	(),
	("input_regs_dis",                                    				  ),
	(                 "high_data_width",                  				  ),
	("input_regs_dis","high_data_width",                  				  ),
	(		          "high_data_width","dsp_dis",        				  ),
	("input_regs_dis","high_data_width","dsp_dis",        				  ),
	(                                             "mode1",				  ),
	("input_regs_dis",                            "mode1",				  ),
	(                                   "dsp_dis","mode1",				  ),
	("input_regs_dis",                  "dsp_dis","mode1",				  ),
	(                                             "mode2",				  ),
	("input_regs_dis",                            "mode2",				  ),
	(                                   "dsp_dis","mode2",				  ),
	("input_regs_dis",                  "dsp_dis","mode2",				  ),
	("input_regs_dis",                                    "device_agilex",),
	(                 "high_data_width",                  "device_agilex",),
	("input_regs_dis","high_data_width",                  "device_agilex",),
	(		          "high_data_width","dsp_dis",        "device_agilex",),
	("input_regs_dis","high_data_width","dsp_dis",        "device_agilex",),
	(                                             "mode1","device_agilex",),
	("input_regs_dis",                            "mode1","device_agilex",),
	(                                   "dsp_dis","mode1","device_agilex",),
	("input_regs_dis",                  "dsp_dis","mode1","device_agilex",),
	(                                             "mode2","device_agilex",),
	("input_regs_dis",                            "mode2","device_agilex",),
	(                                   "dsp_dis","mode2","device_agilex",),
	("input_regs_dis",                  "dsp_dis","mode2","device_agilex",),
	),

}
