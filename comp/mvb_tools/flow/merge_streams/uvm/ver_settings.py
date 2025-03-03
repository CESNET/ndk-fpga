# ver_settings.py
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    # The default setting of verification
    "default" : {
        "MVB_ITEMS"       : "4",
        "MVB_ITEM_WIDTH"  : "32",
        "RX_STREAMS"      : "2",
        "RX_SHAKEDOWN_EN" : "1",
        "SW_TIMEOUT_W"    : "4",
        "DEVICE"          : "\\\"AGILEX\\\"",
        "__core_params__" : {"UVM_TEST": "test::test_base"},
    },
    # MVB_ITEMS
    "mvb_items_big" : {
        "MVB_ITEMS" : "8",
    },
    # MVB_ITEM_WIDTH
    "mvb_item_width_big" : {
        "MVB_ITEM_WIDTH" : "256",
    },
    # RX_STREAMS
    "rx_streams_big" : {
        "RX_STREAMS" : "8",
    },
    # RX_SHAKEDOWN_EN
    "rx_shakedown_disabled" : {
        "RX_SHAKEDOWN_EN" : "0",
    },
    # SW_TIMEOUT_W
    "sw_timeout_w_big" : {
        "SW_TIMEOUT_W" : "16",
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
        ("rx_shakedown_disabled", "device_ultrascale",),
        # TC-3
        ("mvb_items_big", "mvb_item_width_big", "rx_streams_big", "sw_timeout_w_big", "device_stratix10",),

        # Speed tests
        # TC-4
        ("uvm_speed_test",),
        # TC-5
        ("uvm_speed_test", "rx_shakedown_disabled", "device_ultrascale",),
        # TC-6
        ("uvm_speed_test", "mvb_items_big", "mvb_item_width_big", "rx_streams_big", "sw_timeout_w_big", "device_stratix10",),
    ),
}
