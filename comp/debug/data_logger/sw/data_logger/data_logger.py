#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

import nfb
import math
import sys
import json
import argparse


class DataLogger(nfb.BaseComp):

    DT_COMPATIBLE = "netcope,data_logger"

    # MI registers addresses
    _REG_CTRL           = 0
    _REG_STATS          = 4
    _REG_INDEX          = 8
    _REG_SLICE          = 12
    _REG_HIST           = 16
    _REG_VALUE          = 20

    # Statistics id
    _ID_CNTER_CNT       = 0
    _ID_VALUE_CNT       = 1
    _ID_MI_DATA_WIDTH   = 2
    _ID_CTRLO_WIDTH     = 3
    _ID_CTRLI_WIDTH     = 4
    _ID_CNTER_WIDTH     = 5
    _ID_VALUE_WIDTH     = 6
    _ID_VALUE_EN        = 7
    _ID_SUM_EXTRA_WIDTH = 8
    _ID_HIST_BOX_CNT    = 9
    _ID_HIST_BOX_WIDTH  = 10
    _ID_CTRLO           = 11
    _ID_CTRLI           = 12
    _ID_CNTER           = 13
    _ID_VALUE_MIN       = 14
    _ID_VALUE_MAX       = 15
    _ID_VALUE_SUM       = 16
    _ID_VALUE_HIST      = 17

    # _REG_CTRL bits
    _BIT_SW_RST         = 0
    _BIT_RST_DONE       = 1

    # _ID_VALUE_EN bits
    _BIT_MIN_EN         = 0
    _BIT_MAX_EN         = 1
    _BIT_SUM_EN         = 2
    _BIT_HIST_EN        = 3

    def __init__(self, **kwargs):
        super().__init__(**kwargs)

        self.last_stat  = None
        self.last_index = None
        self.last_slice = None
        self.last_hist_addr = None

        self.config = self.load_config()
        self.mi_width = self.config["MI_DATA_WIDTH"]

    def main_ctrl_read(self):
        return {
            "sw_rst":   (self._comp.get_bit(self._REG_CTRL, self._BIT_SW_RST)),
            "rst_done": (self._comp.get_bit(self._REG_CTRL, self._BIT_RST_DONE)),
        }

    def rst(self):
        self._comp.set_bit(self._REG_CTRL, self._BIT_SW_RST)
        self._comp.set_bit(self._REG_CTRL, self._BIT_SW_RST, False)
        if not self._comp.wait_for_bit(self._REG_CTRL, self._BIT_RST_DONE, level=True):
            print("Err: Could not reset data_logger!", file=sys.stderr)

        self.last_stat  = None
        self.last_index = None
        self.last_slice = None
        self.last_hist_addr = None

    def load_slices(self, width):
        slices = math.ceil(width / self.config["MI_DATA_WIDTH"])
        value = 0

        for i in range(0, slices):
            if self.last_slice != i:
                self._comp.write32(self._REG_SLICE, i)
                self.last_slice = i

            value += self._comp.read32(self._REG_VALUE) << (i * self.config["MI_DATA_WIDTH"])

        return value

    def stat_read(self, stat, index=0, en_slices=True):
        if self.last_stat != stat:
            self._comp.write32(self._REG_STATS, stat)
            self.last_stat = stat
        if self.last_index != index:
            self._comp.write32(self._REG_INDEX, index)
            self.last_index = index

        if not en_slices:
            if self.last_slice != 0:
                self._comp.write32(self._REG_SLICE, 0)
                self.last_slice = 0
            return self._comp.read32(self._REG_VALUE)

        if stat == self._ID_CTRLO:
            width = self.config["CTRLO_WIDTH"]
        elif stat == self._ID_CTRLI:
            width = self.config["CTRLI_WIDTH"]
        elif stat == self._ID_CNTER:
            width = self.config["CNTER_WIDTH"]
        elif stat in (self._ID_VALUE_MIN, self._ID_VALUE_MAX):
            width = self.config["VALUE_WIDTH"][index]
        elif stat == self._ID_VALUE_SUM:
            width = self.config["VALUE_WIDTH"][index] + self.config["SUM_EXTRA_WIDTH"][index]
        elif stat == self._ID_VALUE_HIST:
            width = self.config["HIST_BOX_WIDTH"][index]
        else:
            width = self.config["MI_DATA_WIDTH"]

        return self.load_slices(width)

    def hist_read(self, index, addr):
        if self.last_stat != self._ID_VALUE_HIST:
            self._comp.write32(self._REG_STATS, self._ID_VALUE_HIST)
            self.last_stat = self._ID_VALUE_HIST
        if self.last_index != index:
            self._comp.write32(self._REG_INDEX, index)
            self.last_index = index
        if self.last_hist_addr != addr:
            self._comp.write32(self._REG_HIST, addr)
            self.last_hist_addr = addr

        width = self.config["HIST_BOX_WIDTH"][index]
        return self.load_slices(width)

    def load_config(self):
        config = {}
        config["CNTER_CNT"]         = self.stat_read(self._ID_CNTER_CNT,     en_slices=False)
        config["VALUE_CNT"]         = self.stat_read(self._ID_VALUE_CNT,     en_slices=False)
        config["MI_DATA_WIDTH"]     = self.stat_read(self._ID_MI_DATA_WIDTH, en_slices=False)
        config["CTRLO_WIDTH"]       = self.stat_read(self._ID_CTRLO_WIDTH,   en_slices=False)
        config["CTRLI_WIDTH"]       = self.stat_read(self._ID_CTRLI_WIDTH,   en_slices=False)
        config["CNTER_WIDTH"]       = self.stat_read(self._ID_CNTER_WIDTH,   en_slices=False)

        config["VALUE_WIDTH"]       = []
        config["VALUE_EN"]          = []
        config["SUM_EXTRA_WIDTH"]   = []
        config["HIST_BOX_CNT"]      = []
        config["HIST_BOX_WIDTH"]    = []
        config["HIST_STEP"]         = []

        for i in range(0, config["VALUE_CNT"]):
            en_parsed = {}
            en = self.stat_read(self._ID_VALUE_EN, i, en_slices=False)
            en_parsed["MIN"]  = ((en & 0b0001) > 0)
            en_parsed["MAX"]  = ((en & 0b0010) > 0)
            en_parsed["SUM"]  = ((en & 0b0100) > 0)
            en_parsed["HIST"] = ((en & 0b1000) > 0)

            config["VALUE_EN"]       .append(en_parsed)
            config["VALUE_WIDTH"]    .append(self.stat_read(self._ID_VALUE_WIDTH,     i, en_slices=False))
            config["SUM_EXTRA_WIDTH"].append(self.stat_read(self._ID_SUM_EXTRA_WIDTH, i, en_slices=False))
            config["HIST_BOX_CNT"]   .append(self.stat_read(self._ID_HIST_BOX_CNT,    i, en_slices=False))
            config["HIST_BOX_WIDTH"] .append(self.stat_read(self._ID_HIST_BOX_WIDTH,  i, en_slices=False))

            hist_max  = 2 ** config["VALUE_WIDTH"][i]
            hist_step = hist_max / config["HIST_BOX_CNT"][i]
            config["HIST_STEP"].append(hist_step)

        return config

    def load_ctrl(self, out):
        id    = self._ID_CTRLO if out else self._ID_CTRLI
        return self.stat_read(id, 0)

    def set_ctrlo(self, val):
        if self.last_stat != self._ID_CTRLO:
            self._comp.write32(self._REG_STATS, self._ID_CTRLO)
            self.last_stat = self._ID_CTRLO
        if self.last_index != 0:
            self._comp.write32(self._REG_INDEX, 0)
            self.last_index = 0

        slices = math.ceil(self.config["CTRLO_WIDTH"] / self.mi_width)
        for i in range(0, slices):
            if self.last_slice != i:
                self._comp.write32(self._REG_SLICE, i)
                self.last_slice = i

            slice = self.get_bits(val, self.mi_width, i * self.mi_width)
            self._comp.write32(self._REG_VALUE, slice)

    def load_cnter(self, index):
        return self.stat_read(self._ID_CNTER, index)

    def load_value(self, index):
        if self.config['VALUE_CNT'] <= index:
            print("Value out of range", file=sys.stderr)
            return {
                'cnt': 0,
                'min': 0,
                'max': 0,
                'sum': 0,
                'avg': 0,
                'hist': [],
            }

        val = {}
        val["cnt"] = self.stat_read(self._ID_CNTER, index + self.config["CNTER_CNT"])
        if self.config["VALUE_EN"][index]["MIN"]:
            val["min"] = self.stat_read(self._ID_VALUE_MIN, index)
        if self.config["VALUE_EN"][index]["MAX"]:
            val["max"] = self.stat_read(self._ID_VALUE_MAX, index)
        if self.config["VALUE_EN"][index]["SUM"]:
            val["sum"] = self.stat_read(self._ID_VALUE_SUM, index)
            val["avg"] = val["sum"] / val["cnt"] if val["cnt"] != 0 else 0
        if self.config["VALUE_EN"][index]["HIST"]:
            val["hist"] = []
            for b in range(0, self.config["HIST_BOX_CNT"][index]):
                val["hist"].append(self.hist_read(index, b))

        return val

    def get_bits(self, val, width, pos):
        binary = bin(val)[2:]
        end   = - pos
        start = end - width
        if end == 0:
            end = None
        cut = binary[start:end]
        if len(cut) == 0:
            return 0
        else:
            return int(cut, 2)

    def config_to_str(self):
        return json.dumps(self.config, indent=4)

    def stats_to_str(self, hist=False):
        stats = self.main_ctrl_read()
        for i in range(0, self.config['CNTER_CNT']):
            stats['cnter_' + str(i)] = self.load_cnter(i)
        for i in range(0, self.config['VALUE_CNT']):
            val = self.load_value(i)
            if not hist:
                del val['hist']
            stats['value_' + str(i)] = val
        return json.dumps(stats, indent=4)


def parseParams():
    parser = argparse.ArgumentParser(
        description="data_logger control script",
    )

    access = parser.add_argument_group('card access arguments')
    access.add_argument(
        '-d', '--device', default=nfb.libnfb.Nfb.default_device,
        metavar='device', help="device with target FPGA card")
    access.add_argument(
        '-i', '--index', type=int, metavar='index', default=0, help="index inside DevTree")

    common = parser.add_argument_group('common arguments')
    #common.add_argument('-p', '--print', action='store_true', help = """print registers""")
    common.add_argument('--rst', action='store_true', help="reset mem_tester and mem_logger")
    args = parser.parse_args()
    return args


if __name__ == '__main__':
    args = parseParams()
    logger = DataLogger(dev=args.device, index=args.index)

    #if args.print:
    print(logger.config_to_str())
    print(logger.stats_to_str())

    if args.rst:
        logger.rst()
