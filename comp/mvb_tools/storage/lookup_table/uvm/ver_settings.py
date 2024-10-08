# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MVB_ITEMS"         : "4",
        "LUT_DEPTH"         : "128",
        "LUT_WIDTH"         : "32",
        "LUT_ARCH"          : "\\\"AUTO\\\"",
        "SW_WIDTH"          : "32",
        "META_WIDTH"        : "32",
        "OUTPUT_REG"        : "1",
        "DEVICE"            : "\\\"AGILEX\\\"",
    },
    "reg_variant" : {
        "LUT_DEPTH"        : "1",
    },
    "lut_variant" : {
        "LUT_ARCH"         : "\\\"LUT\\\"",
    },
    "bram_variant" : {
        "LUT_ARCH"         : "\\\"BRAM\\\"",
    },
    "items_comb_1" : {
        "MVB_ITEMS"        : "1",
    },
    "items_comb_2" : {
        "MVB_ITEMS"        : "32",
    },
    "not_use_out_reg" : {
        "OUTPUT_REG"       : "0",
    },
    "two_slices" : {
        "LUT_WIDTH"        : "64",
    },
    "four_slices" : {
        "LUT_WIDTH"        : "128",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination

    ("reg_variant",),
    ("lut_variant",),
    ("bram_variant",),
    ("items_comb_1",),
    ("items_comb_2",),
    ("not_use_out_reg",),
    ("two_slices",),
    ("four_slices",),

    ("lut_variant","items_comb_1",),
    ("lut_variant","items_comb_2",),
    ("lut_variant","items_comb_1", "two_slices",),
    ("lut_variant","items_comb_2", "two_slices",),
    ("lut_variant","items_comb_1", "four_slices",),
    ("lut_variant","items_comb_2", "four_slices",),
    ("lut_variant","items_comb_1","not_use_out_reg",),
    ("lut_variant","items_comb_1","not_use_out_reg", "two_slices",),
    ("lut_variant","items_comb_1","not_use_out_reg", "four_slices",),
    ("lut_variant","items_comb_2","not_use_out_reg",),
    ("lut_variant","items_comb_2","not_use_out_reg", "two_slices",),
    ("lut_variant","items_comb_2","not_use_out_reg", "four_slices",),

    ("bram_variant","items_comb_1",),
    ("bram_variant","items_comb_1", "two_slices",),
    ("bram_variant","items_comb_1", "four_slices",),
    ("bram_variant","items_comb_2",),
    ("bram_variant","items_comb_2", "two_slices",),
    ("bram_variant","items_comb_2", "four_slices",),
    ("bram_variant","items_comb_1","not_use_out_reg",),
    ("bram_variant","items_comb_1","not_use_out_reg", "two_slices",),
    ("bram_variant","items_comb_1","not_use_out_reg", "four_slices",),
    ("bram_variant","items_comb_2","not_use_out_reg",),
    ("bram_variant","items_comb_2","not_use_out_reg", "two_slices",),
    ("bram_variant","items_comb_2","not_use_out_reg", "four_slices",),
    ),
}
