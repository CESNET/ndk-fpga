# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
#
# Simple tools for parsing statistics

import numpy as np


class LoggerTools:
    def __init__(self):
        pass

    def nested_dict_keys(self, d, keys=[]):
        for key, value in d.items():
            new_keys = [*keys, key]
            yield new_keys
            if isinstance(value, dict):
                yield from self.nested_dict_keys(value, new_keys)

    def parse_dict_list(self, d_list):
        # Get all keys
        res = {}
        for i in d_list:
            for keys in self.nested_dict_keys(i):
                handle = res
                for k in keys[:-1]:
                    if k not in handle or isinstance(handle[k], list):
                        handle[k] = {}
                    handle = handle[k]

                if keys[-1] not in handle:
                    handle[keys[-1]] = []

        for i in d_list:
            for keys in self.nested_dict_keys(res):
                orig   = i
                handle = res
                for k in keys:
                    handle  = handle[k]
                    if k not in orig:
                        orig = 0    # Default value
                        break
                    orig    = orig[k]

                if isinstance(handle, list):
                    handle.append(orig)

        return res

    def dict_to_numpy(self, d):
        first = d[list(d.keys())[0]]
        res = np.zeros((len(d), len(first)))
        for i, k in enumerate(d):
            res[i] = d[k]

        return res
