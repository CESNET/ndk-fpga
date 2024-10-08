# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "SPLITTER_OUTPUTS"   : "8",
        "REGIONS"            : "4",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "TRANSACTION_COUNT"  : "3000",
        "META_BEHAV"         : "1",
    },
    "region_comb_1" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
    },
    "region_comb_2" : {
        "REGIONS"            : "2",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
    },
    "region_comb_4" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "2",
        "BLOCK_SIZE"         : "4",
    },
    "region_comb_5" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "2",
        "BLOCK_SIZE"         : "8",
    },
    "region_comb_6" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "4",
        "BLOCK_SIZE"         : "8",
    },
    "outputs_2" : {
        "SPLITTER_OUTPUTS"   : "2",
    },
    "outputs_5" : {
        "SPLITTER_OUTPUTS"   : "5",
    },
    "meta_sop" : {
        "META_BEHAV"         : "1",
    },
    "meta_eop" : {
        "META_BEHAV"         : "2",
    },


    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("region_comb_1", "outputs_2", "meta_sop",),
    ("region_comb_2", "outputs_5", "meta_eop",),
    ("region_comb_4", "outputs_2", "meta_eop",),
    ("region_comb_5", "meta_sop",),
    ("region_comb_6", "meta_eop",),
    ),
}
