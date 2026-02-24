# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#            Ondřej Schwarz <ondrejschwarz@cesnet.cz>

from random import randint


def get_mfb_params(signal_bus, params_dic):
    # calculating settings from the bus
    regions = len(signal_bus.sof)
    dw = len(signal_bus.data)
    sof_pos_len = len(signal_bus.sof_pos)

    if (signal_bus.sof_pos is None) or (sof_pos_len == regions):
        sps = 0
    else:
        sps = len(signal_bus.sof_pos) // regions

    if signal_bus.eof_pos is None:
        eps = 0
    else:
        eps = len(signal_bus.eof_pos) // regions

    region_size = 2**sps
    block_size  = 2**(eps - sps)
    item_width  = dw // (regions * region_size * block_size)
    meta_width  = len(signal_bus.meta) // regions if hasattr(signal_bus, "meta") else 0
    os_vld_with = "sof"

    # overriding calculated settings with manual settings (if present)
    if params_dic is not None:
        regions     = params_dic.get("regions", regions)
        region_size = params_dic.get("region_size", region_size)
        block_size  = params_dic.get("block_size", block_size)
        item_width  = params_dic.get("item_width", item_width)
        meta_width  = params_dic.get("meta_width", meta_width)
        os_vld_with = params_dic.get("os_vld_with", os_vld_with)

    # checking for errors
    dw = regions * region_size * block_size * item_width

    if regions != len(signal_bus.sof):
        signal_bus.sof.log.error("MFB parameters do not correspond to signals length!")
        raise Exception()

    if dw != len(signal_bus.data):
        signal_bus.data.log.error("MFB parameters do not correspond to signals length!")
        raise Exception()

    if os_vld_with not in ["sof", "eof"]:
        raise ValueError(f"Invalid value of {os_vld_with} of 'os_vld_with'. Supported values are: \"sof\", \"eof\".")

    return regions, region_size, block_size, item_width, meta_width, os_vld_with


def random_tuple_iterator(min1, max1, min2, max2):
    while True:
        yield (randint(min1, max1), randint(min2, max2))
