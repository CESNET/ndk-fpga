# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#            Ondrej Schwarz <ondrejschwarz@cesnet.cz>

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
def create_setting_from_combination(settings, combination):
    global FAIL
    s = settings["default"].copy()
    for c in combination:
        if c not in settings.keys():
            print("ERROR: Combination \"{}\" contains unknown setting name \"{}\"!".format(combination, c))
            FAIL = True
            continue
        for i in settings[c].keys(): # load modified values
            # if parameter is __coreparams__ then it is dict
            if i == "__core_params__":
                if "__core_params__" not in s.keys():
                    s[i] = settings[c][i]
                else:
                    s[i].update(settings[c][i])
            # or it is string
            elif i not in s.keys():
                print("ERROR: Parameter \"{}\" is present in setting \"{}\" but not in setting \"default\". This might cause unexpected behaviour in the following runs!".format(i, c))
                FAIL = True
                s[i] = settings[c][i]
            else:
                s[i] = settings[c][i]
    return s
