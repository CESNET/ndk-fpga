# ver_settings.py
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    # The default setting of verification
    "default" : {
        "REGIONS"         : "4",
        "REGION_SIZE"     : "8",
        "BLOCK_SIZE"      : "8",
        "ITEM_WIDTH"      : "8",
        "META_WIDTH"      : "8",
        "PKT_MTU"         : "2**14",
        "DEVICE"          : "\\\"AGILEX\\\"",
        "__core_params__" : {"UVM_TEST": "test::test_base"}
    },
    # MFB presets
    "small" : {
        "REGIONS" : "1",
        "PKT_MTU" : "2**12",
    },
    # DEVICE
    "device_stratix10" : {
        "DEVICE" : "\\\"STRATIX10\\\"",
    },
    "device_ultrascale" : {
        "DEVICE" : "\\\"ULTRASCALE\\\"",
    },
    # UVM_TEST
    "uvm_speed_test" : {
        "__core_params__" : {"UVM_TEST": "test::test_speed"}
    },
    # Combinations
    "_combinations_" : (
        # Base tests
        # TC-1
        (), # Works the same as '("default",),' as the "default" is applied in every combination
        # TC-2
        ("small", "device_ultrascale",),

        # Speed tests
        # TC-3
        ("uvm_speed_test", "device_ultrascale"),
        # TC-4
        ("uvm_speed_test", "small",),
    ),
}
