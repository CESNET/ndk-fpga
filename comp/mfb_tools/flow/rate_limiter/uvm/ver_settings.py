# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Tomáš Hak <xhakto01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MI_DATA_WIDTH"   : "32",
        "MI_ADDR_WIDTH"   : "32",

        "MFB_REGIONS"     : "1",
        "MFB_REGION_SIZE" : "8",
        "MFB_BLOCK_SIZE"  : "8",
        "MFB_ITEM_WIDTH"  : "8",
        "MFB_META_WIDTH"  : "8",

        "SECTION_LENGTH"  : "1000",
        "INTERVAL_LENGTH" : "40",
        "INTERVAL_COUNT"  : "32",
        "OUTPUT_SPEED"    : "62500",
        "FREQUENCY"       : "200",

        "DEVICE"          : "\\\"AGILEX\\\"",
    },
    "more_accurate" : {
        "SECTION_LENGTH"  : "4000",
        "INTERVAL_LENGTH" : "10",
        "OUTPUT_SPEED"    : "250000",
    },
    "half_regs" : {
        "INTERVAL_COUNT"  : "16",
    },
    "200G" : {
        "MFB_REGIONS"     : "2",
        "OUTPUT_SPEED"    : "125000",
    },
    "400G" : {
        "MFB_REGIONS"     : "4",
        "OUTPUT_SPEED"    : "250000",
    },
    "400G_more_accurate" : {
        "MFB_REGIONS"     : "4",
        "SECTION_LENGTH"  : "4000",
        "INTERVAL_LENGTH" : "10",
        "OUTPUT_SPEED"    : "1000000",
    },
    "_combinations_" : (
        (), # Works the same as '("default",)' as the "default" is applied in every combination

        ("more_accurate",),
        ("half_regs",),
        ("200G",),
        ("400G",),
        ("400G_more_accurate",),

        ("more_accurate","half_regs",),
        ("200G","half_regs",),
        ("400G","half_regs",),
        ("400G_more_accurate","half_regs",),
    ),
}
