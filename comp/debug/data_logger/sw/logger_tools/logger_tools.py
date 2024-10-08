#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

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

#   ## Printing ##
#
#   def printValue(self, name, key=None, value=None, norm='from main', normV=None):
#       stat        = self.origStat[-1]     #self.stat[-1]
#       if normV is None:
#           normV   = stat[norm]
#
#       if key is None and value is None:
#           return f"{name:<25}\n"
#
#       if value is not None:
#           val     = value
#           rel     = val / normV * 100
#       elif key not in stat or normV <= 0:
#           val     = "-"
#           rel     = "-"
#       else:
#           val     = stat[key]
#           rel     = val / normV * 100
#
#       return f"{name:<25} = {val:<15} [{rel:<.5} %]\n"
#
#   def getHist(self, key):
#       hist = self.origStat[-1][key]
#       hist = {float(k) : v for k,v in hist.items()}
#       return hist
#
#   def sortHist(self, key):
#       hist = self.getHist(key)
#       hist = sorted(hist.items(), key=lambda i: i[0])
#       return hist
#
#   def printHistRaw(self, hist, cut=None):
#       txt = ""
#       if len(hist) == 0:
#           return "  -\n"
#       hist = {float(k) : v for k,v in hist.items()}
#       sort = sorted(hist.items(), key=lambda i: i[0])
#       if cut is not None and len(sort) > 2 * cut + 1:
#           sort = sort[:cut] + [('...', '...')] + sort[len(sort) - cut:]
#
#       for k, v in sort:
#           txt += f"  {k} = {v}\n"
#       return txt
#
#   def topNHistRaw(self, hist, N=5):
#       hist = {float(k) : v for k,v in hist.items()}
#       arr = {k: v for k,v in sorted(hist.items(), key=lambda i: i[0])}
#       top = 0
#       for k,v in arr.items():
#           if k < N:
#               top += v
#           else:
#               break
#       # TODO: div N?
#       topRel = float(top) / self.origStat[-1]['from main'] / N * 100
#       return top, topRel
#
#   def topNHist(self, hist, N=5):
#       if len(hist) < N:
#           return ""
#       else:
#           top, topRel = self.topNHistRaw(hist, N)
#           return f"  top {N} = {top} [{topRel:.2E} %]\n"
#
#   def printHist(self, name, key, cut=5, N=None):
#       stat= self.origStat[-1]     #self.stat[-1]
#       txt = ""
#       txt += f"{name}:\n"
#       if key not in stat:
#           txt += "-\n"
#       else:
#           if N is not None:
#               txt += self.topNHist(stat[key], N=N)
#           txt += self.printHistRaw(stat[key], cut=cut)
#       return txt
