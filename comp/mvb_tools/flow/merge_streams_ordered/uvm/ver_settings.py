# ver_settings.py
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>

# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default" : { # The default setting of verification
        "MVB_ITEMS"             : "2",
        "MVB_ITEM_WIDTH"        : "32",
        "RX_STREAMS"            : "4",
        "USE_FIFOX_MULTI"       : "0",
        "SEL_SHAKEDOWN_EN"      : "0",
        "DEVICE"                : "\\\"AGILEX\\\"",
        "MIN_TRANSACTION_COUNT" : "1000",
        "MAX_TRANSACTION_COUNT" : "2000",
        "ARCH"                  : "\\\"FIFOX\\\"",
        "__core_params__"       : {"UVM_TEST" : "test::ex_test"},
    },

    "rx_comb1" : {
        "MVB_ITEMS"     : "4",
        "RX_STREAMS"    : "8",
    } ,

    "rx_comb2": {
        "MVB_ITEMS"     : "1",
        "RX_STREAMS"    : "32",
    },

    "eff_comb0": {
        "ARCH"              : "\\\"FIFOX\\\"",
        "SEL_SHAKEDOWN_EN"  : "0",
    },

    "eff_comb1": {
        "ARCH"              : "\\\"SHAKEDOWN\\\"",
        "SEL_SHAKEDOWN_EN"  : "1",
    },

    "eff_comb2": {
        "ARCH"              : "\\\"FIFOX\\\"",
        "SEL_SHAKEDOWN_EN"  : "1",
    },

    "eff_simple": {
        "MVB_ITEMS"         : "1",
        "ARCH"              : "\\\"SIMPLE\\\"",
        "SEL_SHAKEDOWN_EN"  : "0",
    },

    "speed": {
        "__core_params__"   : {"UVM_TEST" : "test::speed_test"},
    },

    "_combinations_" : (
        # '()' works the same as '("default",)' as the "default" is applied in every combination

        (),
        ("rx_comb1", "eff_comb0"),
        ("rx_comb2", "eff_comb0"),
        ("rx_comb1", "eff_comb0", "speed"),

        ("rx_comb1", "eff_comb1"),
        ("rx_comb2", "eff_comb1"),
        ("rx_comb1", "eff_comb1", "speed"),

        ("rx_comb1", "eff_comb2"),
        ("rx_comb2", "eff_comb2"),

        ("eff_simple",),
        ("eff_simple", "speed"),

    ),
}
