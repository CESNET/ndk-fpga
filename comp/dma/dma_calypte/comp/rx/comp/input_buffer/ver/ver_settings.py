# ver_settings.py: various sets of input configuration parameters
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-CLause

SETTINGS = {
    "default" : { # The default setting of verification
        "REGIONS"            : "1",
        "REGION_SIZE"        : "4",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "512b" : {
        "REGION_SIZE"        : "8",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("512b",),
    ),
}
