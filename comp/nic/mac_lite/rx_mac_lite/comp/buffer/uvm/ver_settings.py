# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kříž <danielkriz@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MFB_REGIONS"      : "4",
        "MFB_REGION_SIZE"  : "8",
        "MFB_BLOCK_SIZE"   : "8",
        "MFB_ITEM_WIDTH"   : "8",
        "MFB_META_WIDTH"   : "131",
        "DEVICE"           : "\\\"AGILEX\\\"",
        "RX_CLK_PERIOD"    : "2.4ns",
        "TX_CLK_PERIOD"    : "5ns",
        "__core_params__": {"UVM_TEST": "test::ex_test"},
    },
    "mfb_comb_1" : {
        "MFB_REGIONS"      : "1",
        "MFB_REGION_SIZE"  : "4",
        "MFB_BLOCK_SIZE"   : "1",
        "MFB_ITEM_WIDTH"   : "32",
    },
    "mfb_comb_2" : {
        "MFB_REGIONS"      : "1",
        "MFB_REGION_SIZE"  : "4",
        "MFB_BLOCK_SIZE"   : "2",
        "MFB_ITEM_WIDTH"   : "8",
    },
    "device_agilex" : {
        "DEVICE"           : "\\\"AGILEX\\\"",
    },
    "device_stratix" : {
        "DEVICE"           : "\\\"STRATIX10\\\"",
    },
    "device_ultrascale" : {
        "DEVICE"           : "\\\"ULTRASCALE\\\"",
    },
    "device_virtex" : {
        "DEVICE"           : "\\\"7SERIES\\\"",
    },
    "time_comb_1" : {
        "RX_CLK_PERIOD"    : "5ns",
        "TX_CLK_PERIOD"    : "5ns",
    },
    "time_comb_2" : {
        "RX_CLK_PERIOD"    : "8ns",
        "TX_CLK_PERIOD"    : "3.5ns",
    },
    "test_base" : {
        "__core_params__": {"UVM_TEST": "test::ex_test"},
    },
    "test_fast" : {
        "__core_params__": {"UVM_TEST": "test::speed"},
    },

    "_combinations_" : (
    ("default", "device_stratix", "test_base"),
    ("default", "device_ultrascale", "test_base"),
    ("default", "device_agilex", "test_base"),
    ("default", "device_virtex", "test_base"),

    ("default", "device_stratix", "test_fast"),
    ("default", "device_ultrascale", "test_fast"),
    ("default", "device_agilex", "test_fast"),
    ("default", "device_virtex", "test_fast"),

    ("default", "mfb_comb_1", "device_stratix"),
    ("default", "mfb_comb_2", "device_stratix"),

    ("default", "mfb_comb_1", "device_ultrascale"),
    ("default", "mfb_comb_2", "device_ultrascale"),

    ("default", "device_stratix", "time_comb_1"),
    ("default", "device_stratix", "time_comb_2"),
    ("default", "device_ultrascale", "time_comb_1"),
    ("default", "device_ultrascale", "time_comb_2"),
    ),

}
