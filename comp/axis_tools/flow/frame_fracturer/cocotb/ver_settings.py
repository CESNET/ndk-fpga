# ver_settings.py
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default": {
        "AXI_TDATA_WIDTH": "512",
        "MAX_FRACTURES":   "1",
        "SHREG_STAGES":    "2",
        "INPUT_REG":       "False",
    },

    "multi_fracture": {
        "MAX_FRACTURES": "2",
    },

    "shreg_stages_3": {
        "SHREG_STAGES": "3",
    },

    "input_reg": {
        "INPUT_REG": "True",
    },

    "wide_bus": {
        "AXI_TDATA_WIDTH": "2048",
    },

    # Cocotb test parameters (not VHDL generics).
    # Passed to the test as environment variables via __cocotb_params__.
    "transactions_500" : {
        "__cocotb_params__"    : {"FRAME_COUNT": "500"},
    },

    "_combinations_": (
        (),                                                                # default: MAX_FRACTURES=1
        ("multi_fracture", "shreg_stages_3"),                              # MAX_FRACTURES=2, SHREG_STAGES=3
        ("multi_fracture", "input_reg"),                                   # MAX_FRACTURES=2, INPUT_REG=True, 512-bit (PPW use case)
        ("wide_bus", "input_reg", "transactions_500"),                     # AXI_TDATA_WIDTH=2048, INPUT_REG=True
        ("wide_bus", "multi_fracture", "input_reg", "transactions_500"),   # 2048-bit, MAX_FRACTURES=2, INPUT_REG (PPW use case)
    ),
}
