# utils.py: MFB utils
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

def get_mfb_params(signal_data, signal_sof_pos, signal_eof_pos, signal_sof, params_dic):
    if params_dic is None:
        regions = len(signal_sof)
        dw = len(signal_data)

        if signal_sof_pos is None:
            sps = 0
        else:
            sps = len(signal_sof_pos) // regions

        if signal_eof_pos is None:
            eps = 0
        else:
            eps = len(signal_eof_pos) // regions

        region_size = 2**sps
        block_size = 2**(eps - sps)
        item_width = dw // (regions * region_size * block_size)
    else:
        regions = params_dic["regions"]
        region_size = params_dic["region_size"]
        block_size = params_dic["block_size"]
        item_width = params_dic["item_width"]

        dw = regions * region_size * block_size * item_width

        if regions != len(signal_sof):
            signal_sof.log.error("MFB parameters do not correspond to signals length!")
            raise Exception()

        if dw != len(signal_data):
            signal_data.log.error("MFB parameters do not correspond to signals length!")
            raise Exception()

    #print(regions)
    #print(region_size)
    #print(block_size)
    #print(item_width)

    return regions, region_size, block_size, item_width


def signal_unpack(items, signal):
    signal_arr = [0] * items

    if signal is None:
        return signal_arr

    size = len(signal) // items

    for ii in range(items):
        bi = (items - ii - 1) * size
        signal_arr[ii] = signal.value[bi:(bi + size - 1)].integer

    return signal_arr
