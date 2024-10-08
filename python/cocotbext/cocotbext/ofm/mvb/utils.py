# utils.py: MVB utils
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import random


def random_delays_config(items: int, params_dic: dict) -> (dict, int, int):
    """
    Generate configuration of random delay generator based on passed dictionary.
    If no dictionary was passed, configuratoin is generated with default parameters.

        Args:
            items: number of MVB items.
            params_dic: dictionary with MVB parameters.

        Returns:
            cDelays: settings of random delays.
            mode: fill delay with: mode 0 - previous transaction,
                mode 1 - 0, mode 2 - random integer from 0-256, mode 3 - with ascii value of X
            delays_fill: the character, with which the delays will be filled with.
    """
    cDelays = dict()

    mode = params_dic.get("mode", 1)

    # parameters for whole invalid words
    wordDelayEnable_wt = params_dic.get("wordDelayEnable_wt", 10)
    wordDelayDisable_wt = params_dic.get("wordDelayDisable_wt", 90)
    wordDelayLow = params_dic.get("wordDelayLow", 0)
    wordDelayHigh = params_dic.get("wordDelayHigh", 50)

    # parameters for whole invalid items
    ivgEnable_wt = params_dic.get("ivgEnable_wt", 3)
    ivgDisable_wt = params_dic.get("ivgDisable_wt", 1)
    ivgLow = params_dic.get("ivgLow", 0)
    ivgHigh = params_dic.get("ivgHigh", 2 * items - 1)

    cDelays["wordDelayEn_wt"] = (wordDelayDisable_wt, wordDelayEnable_wt)
    cDelays["wordDelay"] = range(wordDelayLow, wordDelayHigh)
    cDelays["ivgEn_wt"] = (ivgDisable_wt, ivgEnable_wt)
    cDelays["ivg"] = range(ivgLow, ivgHigh)

    delays_fill = {
        0: None,
        1: 0,
        2: random.randrange(0, 256),
        3: ord('X'),
    }[mode]

    return cDelays, mode, delays_fill
