# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MFB_REGIONS"       : "2",
        "MFB_REGION_SIZE"   : "1",
        "MFB_BLOCK_SIZE"    : "8",
        "MFB_ITEM_WIDTH"    : "32",
        "HDR_SIZE"          : "4",
        "MVB_ITEMS"         : "2",
        "FRAME_SIZE_MIN"    : "1",
        "FRAME_SIZE_MAX"    : "50",
        "TRANSACTION_COUNT" : "2000",
    },
    "pcie" : {
        "MFB_REGIONS"       : "2",
        "MFB_REGION_SIZE"   : "1",
        "MFB_BLOCK_SIZE"    : "8",
        "MFB_ITEM_WIDTH"    : "32",
    },
    "region_comb_1" : {
        "MFB_REGIONS"       : "1",
        "MFB_REGION_SIZE"   : "8",
        "MFB_BLOCK_SIZE"    : "8",
        "MFB_ITEM_WIDTH"    : "8",
    },
    "region_comb_2" : {
        "MFB_REGIONS"       : "2",
        "MFB_REGION_SIZE"   : "8",
        "MFB_BLOCK_SIZE"    : "8",
        "MFB_ITEM_WIDTH"    : "8",
    },
    "region_comb_3" : {
        "MFB_REGIONS"       : "1",
        "MFB_REGION_SIZE"   : "1",
        "MFB_BLOCK_SIZE"    : "8",
        "MFB_ITEM_WIDTH"    : "8",
    },
    "region_comb_4" : {
        "MFB_REGIONS"       : "1",
        "MFB_REGION_SIZE"   : "2",
        "MFB_BLOCK_SIZE"    : "4",
        "MFB_ITEM_WIDTH"    : "8",
    },
    "region_comb_5" : {
        "MFB_REGIONS"       : "1",
        "MFB_REGION_SIZE"   : "2",
        "MFB_BLOCK_SIZE"    : "8",
        "MFB_ITEM_WIDTH"    : "8",
    },
    "region_comb_6" : {
        "MFB_REGIONS"       : "1",
        "MFB_REGION_SIZE"   : "4",
        "MFB_BLOCK_SIZE"    : "8",
        "MFB_ITEM_WIDTH"    : "8",
    },
    "hdr_size_comb_min" : {
        "HDR_SIZE"          : "1",
    },
    "hdr_size_comb_1" : {
        "HDR_SIZE"          : "8",
    },
    "hdr_size_comb_2" : {
        "HDR_SIZE"          : "32",
    },
    "mvb_items_comb_1" : {
        "MVB_ITEMS"         : "1",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("region_comb_1","mvb_items_comb_1",),
    ("region_comb_2",),
    ("region_comb_3","mvb_items_comb_1",),
    ("region_comb_4","mvb_items_comb_1",),
    ("region_comb_5","mvb_items_comb_1",),
    ("region_comb_6","mvb_items_comb_1",),
    ("pcie",),

    ("hdr_size_comb_min",),
    ("hdr_size_comb_1",),
    ("hdr_size_comb_2",),

    ("region_comb_1","mvb_items_comb_1","hdr_size_comb_min",),
    ("region_comb_1","mvb_items_comb_1","hdr_size_comb_1",),
    ("region_comb_1","mvb_items_comb_1","hdr_size_comb_2",),
    ("region_comb_1","mvb_items_comb_1",),

    ("region_comb_2","hdr_size_comb_min",),
    ("region_comb_2","hdr_size_comb_1",),
    ("region_comb_2","hdr_size_comb_2",),
    ("region_comb_2",),

    ("region_comb_3","mvb_items_comb_1","hdr_size_comb_min",),
    ("region_comb_3","mvb_items_comb_1","hdr_size_comb_1",),
    ("region_comb_3","mvb_items_comb_1","hdr_size_comb_2",),
    ("region_comb_3","mvb_items_comb_1",),

    ("region_comb_4","mvb_items_comb_1","hdr_size_comb_min",),
    ("region_comb_4","mvb_items_comb_1","hdr_size_comb_1",),
    ("region_comb_4","mvb_items_comb_1","hdr_size_comb_2",),
    ("region_comb_4","mvb_items_comb_1",),

    ("region_comb_5","mvb_items_comb_1","hdr_size_comb_min",),
    ("region_comb_5","mvb_items_comb_1","hdr_size_comb_1",),
    ("region_comb_5","mvb_items_comb_1","hdr_size_comb_2",),
    ("region_comb_5","mvb_items_comb_1",),

    ("region_comb_6","mvb_items_comb_1","hdr_size_comb_min",),
    ("region_comb_6","mvb_items_comb_1","hdr_size_comb_1",),
    ("region_comb_6","mvb_items_comb_1","hdr_size_comb_2",),
    ("region_comb_6","mvb_items_comb_1",),

    ("pcie","hdr_size_comb_min",),
    ("pcie","hdr_size_comb_1",),
    ("pcie","hdr_size_comb_2",),
    ("pcie",),
    ),
}
