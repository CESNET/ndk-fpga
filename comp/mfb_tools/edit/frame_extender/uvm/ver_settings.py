# ver_settings.py
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    # The default setting of verification
    "default" : {
        "MFB_REGIONS"     : "4",
        "MFB_REGION_SIZE" : "8",
        "MFB_BLOCK_SIZE"  : "8",
        "MFB_ITEM_WIDTH"  : "8",
        "PKT_MTU"         : "2**14",
        "MVB_FIFO_DEPTH"  : "32",
        "MFB_FIFO_DEPTH"  : "32",
        "USERMETA_WIDTH"  : "32",
        "DEVICE"          : "\\\"AGILEX\\\"",
        "__core_params__" : {"UVM_TEST": "test::test_base"}
    },
    # MFB presets
    "single_region" : {
        "MFB_REGIONS" : "1",
    },
    "big_fifos" : {
        "MVB_FIFO_DEPTH" : "512",
        "MFB_FIFO_DEPTH" : "512",
    },
    # DEVICE
    "device_stratix10" : {
        "DEVICE" : "\\\"STRATIX10\\\"",
    },
    "device_ultrascale" : {
        "DEVICE" : "\\\"ULTRASCALE\\\"",
    },
    "device_7series" : {
        "DEVICE" : "\\\"7SERIES\\\"",
    },
    # UVM_TEST
    "uvm_speed_test" : {
        "__core_params__" : {"UVM_TEST": "test::test_speed"}
    },

    # Combinations
    "_combinations_" : (
        # Base tests
        # TC-1
        (), # Works the same as `("default",),` as the "default" is applied in every combination
        # TC-2
        ("single_region", "device_stratix10",),
        # TC-3
        ("big_fifos", "device_ultrascale",),

        # Speed tests
        # TC-4
        ("uvm_speed_test", "device_7series",),
        # TC-5
        ("uvm_speed_test", "single_region", "device_ultrascale"),
        # TC-6
        ("uvm_speed_test", "big_fifos", "device_stratix10",),
    ),
}
