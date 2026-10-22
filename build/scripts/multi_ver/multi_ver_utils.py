# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#            Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import copy
from random import randint


# RANDOMLY reduce number of combination to a certain percentage
def reduce_combinations(combinations, reduction_perc=100):
    if reduction_perc >= 100:
        return combinations

    items = len(combinations)
    new_items = items * reduction_perc // 100
    if new_items < 1:
        new_items = 1

    comb = list(combinations.keys())
    new_comb = dict()
    for i in range(new_items):
        new_item_key = comb.pop(randint(0, len(comb) - 1))
        new_comb[new_item_key] = combinations[new_item_key]

    return new_comb


# Modify setting variable
# Raises ValueError when the combination cannot be created as written
def create_setting_from_combination(settings, combination):
    if isinstance(combination, str):
        raise ValueError("Combination \"{}\" is a string, not a tuple. Add a trailing comma.".format(combination))
    # Deep copy, so the merged dicts below do not change the settings
    s = copy.deepcopy(settings["default"])
    for c in combination:
        if c not in settings.keys():
            raise ValueError("Combination \"{}\" contains unknown setting name \"{}\"!".format(combination, c))
        for i in settings[c].keys(): # load modified values
            # if parameter is a dict then merge it
            if i in ("__core_params__", "__cocotb_params__"):
                s.setdefault(i, {}).update(settings[c][i])
            # or it is string
            elif i not in s.keys():
                raise ValueError("Parameter \"{}\" is present in setting \"{}\" but not in setting \"default\"!".format(i, c))
            else:
                s[i] = settings[c][i]
    return s
