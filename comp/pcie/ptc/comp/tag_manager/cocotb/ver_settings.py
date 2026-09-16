# ver_settings.py
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default": {
        "PCIE_TAG_WIDTH": "8",
        # Every generic that a combination below overrides has to be listed here.
        # multi_ver_cocotb.py fails the whole run when a key is missing from
        # "default". Both values below are the defaults of the entity itself.
        "CHECK_CPL_CREDITS": "False",
        "EXTRA_WORDS": "512",
    },
    "pcie_tag_width_10b": {
        # 512 tags instead of 256, which is the tag pool of the Intel P-Tile and R-Tile
        "PCIE_TAG_WIDTH": "10",
    },
    "credit_check": {
        "CHECK_CPL_CREDITS": "True",
        # Much smaller than the tag pool needs. With the default EXTRA_WORDS the
        # tags run out first and enough_free_cplh never stops anything.
        "EXTRA_WORDS": "8",
    },
}

SETTINGS["_combinations_"] = (
    (),                            # PCIE_TAG_WIDTH=8, 256 tags
    ("pcie_tag_width_10b",),       # PCIE_TAG_WIDTH=10, 512 tags
    ("credit_check",),             # the Storage FIFOX word budget is the limit
)
