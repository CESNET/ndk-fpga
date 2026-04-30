SETTINGS = {
    # default combination. All parameters have to be in
    # package with generic. For example generic.sv
    "default" : {
        "ITEMS"               : 64,
        "ITEM_WIDTH"          : 8,
        "TUSER_WIDTH"         : 2,
        "FIFO_ITEMS"          : 512,
        "RAM_TYPE"            : "BRAM",
        "FWFT_MODE"           : 1,
        "OUTPUT_REG"          : 1,
        "AFULL_OFFSET"        : 256, # FIFO_ITEMS/2
        "AEMPTY_OFFSET"       : 256, # FIFO_ITEMS/2
        "DEVICE"              : "AGILEX",
        # Core params setup variable in environment
        "__core_params__"  : {"UVM_TEST" : "test::base" },
    },
    "width_1": {
        "ITEMS"               : 17,
        "ITEM_WIDTH"          : 23,
        "TUSER_WIDTH"         : 5,
    },
    "width_2": {
        "ITEMS"               : 139,
        "ITEM_WIDTH"          : 17,
        "TUSER_WIDTH"         : 30,
    },
    "fifo_1": {
        "FIFO_ITEMS"          : 2,
        "AFULL_OFFSET"        : 1,
        "AEMPTY_OFFSET"       : 1,
    },
    "fifo_2": {
        "FIFO_ITEMS"          : 247,
        "AFULL_OFFSET"        : 30,
        "AEMPTY_OFFSET"       : 20,
    },
    "fifo_3": {
        "FIFO_ITEMS"          : 111,
        "AFULL_OFFSET"        : 90,
        "AEMPTY_OFFSET"       : 100,
    },
    "fwft_mode_0": {
        "FWFT_MODE"           : 0,
    },
    "output_reg_0": {
        "OUTPUT_REG"          : 0,
    },
    # test uses combination setup above
    "_combinations_" : {
        "test_name_0"  :  ("default", ),
        "test_name_1"  :  ("default", "width_1", "fifo_1"),
        "test_name_2"  :  ("default", "width_1", "fifo_1", "fwft_mode_0"),
        "test_name_3"  :  ("default", "width_1", "fifo_1", "output_reg_0"),
        "test_name_4"  :  ("default", "width_1", "fifo_1", "fwft_mode_0", "output_reg_0"),
        "test_name_5"  :  ("default", "width_1", "fifo_2"),
        "test_name_6"  :  ("default", "width_1", "fifo_2", "fwft_mode_0"),
        "test_name_7"  :  ("default", "width_1", "fifo_2", "output_reg_0"),
        "test_name_8"  :  ("default", "width_1", "fifo_2", "fwft_mode_0", "output_reg_0"),
        "test_name_9"  :  ("default", "width_1", "fifo_3"),
        "test_name_10" :  ("default", "width_1", "fifo_3", "fwft_mode_0"),
        "test_name_11" :  ("default", "width_1", "fifo_3", "output_reg_0"),
        "test_name_12" :  ("default", "width_1", "fifo_3", "fwft_mode_0", "output_reg_0"),
        "test_name_13" :  ("default", "width_2", "fifo_1"),
        "test_name_14" :  ("default", "width_2", "fifo_1", "fwft_mode_0"),
        "test_name_15" :  ("default", "width_2", "fifo_1", "output_reg_0"),
        "test_name_16" :  ("default", "width_2", "fifo_1", "fwft_mode_0", "output_reg_0"),
        "test_name_17" :  ("default", "width_2", "fifo_2"),
        "test_name_18" :  ("default", "width_2", "fifo_2", "fwft_mode_0"),
        "test_name_19" :  ("default", "width_2", "fifo_2", "output_reg_0"),
        "test_name_20" :  ("default", "width_2", "fifo_2", "fwft_mode_0", "output_reg_0"),
        "test_name_21" :  ("default", "width_2", "fifo_3"),
        "test_name_22" :  ("default", "width_2", "fifo_3", "fwft_mode_0"),
        "test_name_23" :  ("default", "width_2", "fifo_3", "output_reg_0"),
        "test_name_24" :  ("default", "width_2", "fifo_3", "fwft_mode_0", "output_reg_0"),
    }
}
