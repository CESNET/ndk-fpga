# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "ITEMS"             : "4",
        "ITEM_WIDTH"        : "16",
        "SRC_CHANNELS"      : "16",
        "DST_CHANNELS"      : "32",
        "REG_SETTINGS"      : "0",
        "TRANSACTION_COUNT" : "10000",
    },
    "bus_comb_1" : {
        "ITEM_WIDTH"        : "8",
    },
    "bus_comb_2" : {
        "ITEM_WIDTH"        : "32",
    },
    "bus_comb_3" : {
        "ITEM_WIDTH"        : "77",
    },
    "items_comb_1" : {
        "ITEMS"             : "8",
    },
    "items_comb_2" : {
        "ITEMS"             : "1",
    },
    "src_same_as_dst_channels" : {
        "SRC_CHANNELS"      : "16",
        "DST_CHANNELS"      : "16",
    },
    "dst_channels_max" : {
        "DST_CHANNELS"      : "255",
    },
    "reg_settings_1" : {
        "REG_SETTINGS"      : "1",
    },
    "reg_settings_2" : {
        "REG_SETTINGS"      : "2",
    },
    "reg_settings_3" : {
        "REG_SETTINGS"      : "3",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("src_same_as_dst_channels",),
    ("bus_comb_1",),
    ("bus_comb_1","reg_settings_1","dst_channels_max",),
    ("bus_comb_1","reg_settings_2","dst_channels_max",),
    ("bus_comb_1","reg_settings_3","dst_channels_max",),
    ("bus_comb_1","src_same_as_dst_channels",),
    ("bus_comb_2",),
    ("bus_comb_2","reg_settings_1","dst_channels_max",),
    ("bus_comb_2","reg_settings_2","dst_channels_max",),
    ("bus_comb_2","reg_settings_3","dst_channels_max",),
    ("bus_comb_2","src_same_as_dst_channels",),
    ("bus_comb_3",),
    ("bus_comb_3","reg_settings_1","dst_channels_max",),
    ("bus_comb_3","reg_settings_2","dst_channels_max",),
    ("bus_comb_3","reg_settings_3","dst_channels_max",),
    ("bus_comb_3","src_same_as_dst_channels",),

    ("items_comb_1",),
    ("items_comb_1","reg_settings_1","dst_channels_max",),
    ("items_comb_1","reg_settings_2","dst_channels_max",),
    ("items_comb_1","reg_settings_3","dst_channels_max",),
    ("items_comb_1","src_same_as_dst_channels",),
    ("items_comb_1","bus_comb_1",),
    ("items_comb_1","bus_comb_1","reg_settings_1","dst_channels_max",),
    ("items_comb_1","bus_comb_1","reg_settings_2","dst_channels_max",),
    ("items_comb_1","bus_comb_1","reg_settings_3","dst_channels_max",),
    ("items_comb_1","bus_comb_1","src_same_as_dst_channels",),
    ("items_comb_1","bus_comb_2",),
    ("items_comb_1","bus_comb_2","reg_settings_1","dst_channels_max",),
    ("items_comb_1","bus_comb_2","reg_settings_2","dst_channels_max",),
    ("items_comb_1","bus_comb_2","reg_settings_3","dst_channels_max",),
    ("items_comb_1","bus_comb_2","src_same_as_dst_channels",),
    ("items_comb_1","bus_comb_3",),
    ("items_comb_1","bus_comb_3","reg_settings_1","dst_channels_max",),
    ("items_comb_1","bus_comb_3","reg_settings_2","dst_channels_max",),
    ("items_comb_1","bus_comb_3","reg_settings_3","dst_channels_max",),
    ("items_comb_1","bus_comb_3","src_same_as_dst_channels",),

    ("items_comb_2",),
    ("items_comb_2","reg_settings_1","dst_channels_max",),
    ("items_comb_2","reg_settings_2","dst_channels_max",),
    ("items_comb_2","reg_settings_3","dst_channels_max",),
    ("items_comb_2","src_same_as_dst_channels",),
    ("items_comb_2","bus_comb_1",),
    ("items_comb_2","bus_comb_1","reg_settings_1","dst_channels_max",),
    ("items_comb_2","bus_comb_1","reg_settings_2","dst_channels_max",),
    ("items_comb_2","bus_comb_1","reg_settings_3","dst_channels_max",),
    ("items_comb_2","bus_comb_1","src_same_as_dst_channels",),
    ("items_comb_2","bus_comb_2",),
    ("items_comb_2","bus_comb_2","reg_settings_1","dst_channels_max",),
    ("items_comb_2","bus_comb_2","reg_settings_2","dst_channels_max",),
    ("items_comb_2","bus_comb_2","reg_settings_3","dst_channels_max",),
    ("items_comb_2","bus_comb_2","src_same_as_dst_channels",),
    ("items_comb_2","bus_comb_3",),
    ("items_comb_2","bus_comb_3","reg_settings_1","dst_channels_max",),
    ("items_comb_2","bus_comb_3","reg_settings_2","dst_channels_max",),
    ("items_comb_2","bus_comb_3","reg_settings_3","dst_channels_max",),
    ("items_comb_2","bus_comb_3","src_same_as_dst_channels",),
    ),
}
