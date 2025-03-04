# ver_settings.py
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    # The default setting of verification
    "default" : {
        "RX_ITEMS"        : "4",
        "TX_ITEMS"        : "1",
        "ITEM_WIDTH"      : "128",
        "SHAKE_PORTS"     : "2",
        "USE_MUX_IMPL"    : "0",
        "DEVICE"          : "\\\"AGILEX\\\"",
        "__core_params__" : {"UVM_TEST": "test::test_base"}
    },
    # RX_ITEMS
    "rx_items_big" : {
        "RX_ITEMS" : "8",
    },
    # TX_ITEMS
    "tx_items_big" : {
        "TX_ITEMS" : "8",
    },
    # ITEM_WIDTH
    "item_width_big" : {
        "ITEM_WIDTH" : "256",
    },
    # SHAKE_PORTS
    "shake_ports_min" : {
        "SHAKE_PORTS" : "1",
    },
    "shake_ports_max" : {
        "SHAKE_PORTS" : "3",
    },
    # USE_MUX_IMPL
    "use_mux_impl" : {
        "USE_MUX_IMPL" : "1",
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
        ("use_mux_impl", "shake_ports_min", "device_stratix10",),
        # TC-3
        ("rx_items_big", "tx_items_big", "item_width_big", "shake_ports_max", "device_ultrascale",),

        # Speed tests
        # TC-4
        ("uvm_speed_test",),
        # TC-5
        ("uvm_speed_test", "use_mux_impl", "shake_ports_min", "device_stratix10",),
        # TC-6
        ("uvm_speed_test", "rx_items_big", "tx_items_big", "item_width_big", "shake_ports_max", "device_ultrascale",),
    ),
}
