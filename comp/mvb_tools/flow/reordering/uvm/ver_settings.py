# ver_settings.py
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s):
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    # The default setting of verification
    "default" : {
        "ITEMS"     : "4",
        "ITEM_WIDTH" : "64",
        "OUT_REG_EN"  : "1",
        "REORDERING_EN"  : "1",
        "__core_params__" : {"UVM_TEST": "test::test_base"}

    },
    # MFB presets
    "single_item" : {
        "ITEMS" : "1",
        "REORDERING_EN"  : "0",
    },
    # Irregular Item Count
    "ireg_item_count" : {
        "ITEMS" : "5",
        "REORDERING_EN"  : "1",
    },
    # ITEM_WIDTH
    "item_width_big" : {
        "ITEM_WIDTH" : "5",
    },
    # OUT_REG disable
    "out_reg_disabled" : {
        "OUT_REG_EN"  : "0",
    },

    # Combinations
    "_combinations_" : (
        # Base tests
        #
        (), # Works the same as `("default",),` as the "default" is applied in every combination
        #
        ("single_item",),
        #
        ("item_width_big",),
        #
        ("single_item","item_width_big",),
        #
        ("out_reg_disabled",),

    ),
}
