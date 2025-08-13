# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>

from random import randint


def get_mfb_params(signal_bus, params_dic):
    if params_dic is None:
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
        block_size = 2**(eps - sps)
        item_width = dw // (regions * region_size * block_size)

        if hasattr(signal_bus, "meta"):
            meta_width = len(signal_bus.meta) // regions
        else:
            meta_width = 0
    else:
        regions = params_dic["regions"]
        region_size = params_dic["region_size"]
        block_size = params_dic["block_size"]
        item_width = params_dic["item_width"]
        if "meta_width" in params_dic.keys():
            meta_width = params_dic["meta_width"]
        else:
            meta_width = 0

        dw = regions * region_size * block_size * item_width

        if regions != len(signal_bus.sof):
            signal_bus.sof.log.error("MFB parameters do not correspond to signals length!")
            raise Exception()

        if dw != len(signal_bus.data):
            signal_bus.data.log.error("MFB parameters do not correspond to signals length!")
            raise Exception()

    return regions, region_size, block_size, item_width, meta_width


def random_tuple_iterator(min1, max1, min2, max2):
    while True:
        yield (randint(min1, max1), randint(min2, max2))
