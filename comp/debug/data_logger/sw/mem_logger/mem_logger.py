#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

import json
import argparse
import nfb
from data_logger.data_logger import DataLogger


class MemLogger(DataLogger):

    DT_COMPATIBLE = "netcope,mem_logger"

    _BIT_LATENCY_TO_FIRST    = 0

    def __init__(self, **kwargs):
        try:
            super().__init__(**kwargs)

            ctrli = self.load_ctrl(False)
            self.config["MEM_DATA_WIDTH"]   = self.get_bits(ctrli, self.mi_width, self.mi_width * 0)
            self.config["MEM_ADDR_WIDTH"]   = self.get_bits(ctrli, self.mi_width, self.mi_width * 1)
            self.config["MEM_BURST_WIDTH"]  = self.get_bits(ctrli, self.mi_width, self.mi_width * 2)
            self.config["MEM_FREQ_KHZ"]     = self.get_bits(ctrli, self.mi_width, self.mi_width * 3)

        except Exception:
            print("ERROR while opening MemLogger component!\nMaybe unsupported FPGA firmware?!")
            exit(1)

    def set_config(self, latency_to_first):
        self.set_ctrlo(latency_to_first & 1)

    def ticks_to_s(self, ticks):
        return ticks / (self.config["MEM_FREQ_KHZ"] * 1000.0)

    def ticks_to_flow(self, words, ticks):
        s = self.ticks_to_s(ticks)
        if s == 0:
            return 0
        return (words * self.config["MEM_DATA_WIDTH"]) / s

    # Remove leading and trailing zeros
    def trim_hist(self, data):
        res = {}
        res_tmp = {}

        started = False
        for k, v in data.items():
            if v != 0 or started:
                res_tmp[k] = v
                started = True
            elif v == 0 or not started:
                res_tmp = {k: v}
            if v != 0:
                res = res_tmp.copy()

        return res

    def latency_hist_step(self):
        hist_max  = 2 ** self.config["VALUE_WIDTH"][0]
        hist_step = hist_max / self.config["HIST_BOX_CNT"][0]
        return self.ticks_to_s(hist_step - 1) * 10**9

    def load_stats(self):
        stats = {}

        ctrlo = self.load_ctrl(True)
        stats["latency_to_first"] = (ctrlo >> self._BIT_LATENCY_TO_FIRST) & 1

        # Cnters
        stats["wait"]           = self.load_cnter(0)
        stats["request_hold"]   = self.load_cnter(1)
        stats["rdy_hold_write"] = self.load_cnter(2)
        stats["rdy_hold_read"]  = self.load_cnter(3)

        stats["wr_ticks"]       = self.load_cnter(4)
        stats["rd_ticks"]       = self.load_cnter(5)
        stats["total_ticks"]    = self.load_cnter(6)
        stats["wr_req_cnt"]     = self.load_cnter(7)
        stats["wr_req_words"]   = self.load_cnter(8)
        stats["rd_req_cnt"]     = self.load_cnter(9)
        stats["rd_req_words"]   = self.load_cnter(10)
        stats["rd_resp_words"]  = self.load_cnter(11)
        stats["err_zero_burst"] = self.load_cnter(12)
        stats["err_simult_rw"]  = self.load_cnter(13)

        # Values
        stats["latency"]        = self.load_value(0)
        if self.config["VALUE_CNT"] > 1:
            stats["paralel_read"]   = self.load_value(1)

        # Calculate time and flow
        stats["wr_time_ms"]     = self.ticks_to_s(stats['wr_ticks']) * 10**3
        stats["wr_flow_gbs"]    = self.ticks_to_flow(stats['wr_req_words'], stats['wr_ticks']) / 10**9

        stats["rd_time_ms"]     = self.ticks_to_s(stats['rd_ticks']) * 10**3
        stats["rd_flow_gbs"]    = self.ticks_to_flow(stats['rd_resp_words'], stats['rd_ticks']) / 10**9

        stats["total_time_ms"]  = self.ticks_to_s(stats['total_ticks']) * 10**3
        stats["total_flow_gbs"] = self.ticks_to_flow(stats['wr_req_words'] + stats['rd_resp_words'], stats['total_ticks']) / 10**9

        # Calculate latency
        stats["latency"]["min_ns"]  = self.ticks_to_s(stats["latency"]["min"]) * 10**9
        stats["latency"]["max_ns"]  = self.ticks_to_s(stats["latency"]["max"]) * 10**9
        stats["latency"]["avg_ns"]  = self.ticks_to_s(stats["latency"]["avg"]) * 10**9

        # Calculate latency histogram
        hist_step = self.config["HIST_STEP"][0]
        stats["latency"]["hist_ns"] = {}

        for i, v in enumerate(stats["latency"]["hist"]):
            end   = self.ticks_to_s((i + 1) * hist_step - 1) * 10**9
            stats["latency"]["hist_ns"][end] = v
        stats["latency"]["hist_ns"] = self.trim_hist(stats["latency"]["hist_ns"])

        return stats

    def stats_to_json(self, stats):
        res = json.dumps(stats, indent=4)
        print(res)

    def line_to_str(self, txt, val, unit=""):
        if isinstance(val, int):
            val = f"{val:<15}"
        elif isinstance(val, float):
            val = f"{val:< .2f}"

        if unit != "":
            unit = f"[{unit}]"
        return f"{txt:<20} {val} {unit}\n"

    def stats_to_str(self, stats):
        res = ""
        res += "Mem_logger statistics:\n"
        res += "----------------------\n"
        res += self.line_to_str("write requests   ", stats['wr_req_cnt'])
        res += self.line_to_str("  write words    ", stats['wr_req_words'])
        res += self.line_to_str("read requests    ", stats['rd_req_cnt'])
        res += self.line_to_str("  requested words", stats['rd_req_words'])
        res += self.line_to_str("  received words ", stats['rd_resp_words'])
        res += "Handshakes:\n"
        res += self.line_to_str("  avmm rdy hold      ", stats['rdy_hold_read'] + stats['rdy_hold_write'])
        res += self.line_to_str("  avmm rdy hold (rd) ", stats['rdy_hold_read'])
        res += self.line_to_str("  avmm rdy hold (wr) ", stats['rdy_hold_write'])
        res += self.line_to_str("  no request         ", stats["request_hold"])
        res += self.line_to_str("  wait               ", stats["wait"])
        res += "Flow:\n"
        res += self.line_to_str("  write", stats['wr_flow_gbs'],      "Gb/s")
        res += self.line_to_str("  read ", stats['rd_flow_gbs'],      "Gb/s")
        res += self.line_to_str("  total", stats['total_flow_gbs'],   "Gb/s")
        res += "Time:\n"
        res += self.line_to_str("  write", stats['wr_time_ms'],       "ms")
        res += self.line_to_str("  read ", stats['rd_time_ms'],       "ms")
        res += self.line_to_str("  total", stats['total_time_ms'],    "ms")
        res += "Latency:\n"
        res += self.line_to_str("  min",   stats['latency']["min_ns"], "ns")
        res += self.line_to_str("  max",   stats['latency']["max_ns"], "ns")
        res += self.line_to_str("  avg",   stats['latency']["avg_ns"], "ns")
        res += "  histogram [ns]:\n"
        if len(stats['latency']['hist_ns']) > 0:
            prev = 0
            for k, v in stats['latency']['hist_ns'].items():
                if v != 0:
                    res += self.line_to_str(f"    {prev:> 6.1f} -{k:> 6.1f} ...", v)
                prev = k
        res += "Errors:\n"
        res += self.line_to_str("  zero burst count", stats['err_zero_burst'])
        res += self.line_to_str("  simultaneous r+w", stats['err_simult_rw'])

        if self.config['VALUE_CNT'] > 1:
            res += "Paralel reads count:\n"
            res += self.line_to_str("  min",   stats['paralel_read']["min"], "")
            res += self.line_to_str("  max",   stats['paralel_read']["max"], "")
            res += self.line_to_str("  avg",   stats['paralel_read']["avg"], "")

            hist_step = self.config["HIST_STEP"][1]
            prev = 0
            for i, v in enumerate(stats["paralel_read"]["hist"]):
                if v != 0:
                    res += self.line_to_str(f"    {prev:> 6.1f} -{hist_step * (i + 1):> 6.1f} ...", v)
                    prev = hist_step * (i + 1)

        return res

    def config_to_str(self):
        res = ""
        res += "Mem_logger config:\n"
        res += "------------------\n"
        res += f"MEM_DATA_WIDTH:     {self.config['MEM_DATA_WIDTH']}\n"
        res += f"MEM_ADDR_WIDTH:     {self.config['MEM_ADDR_WIDTH']}\n"
        res += f"MEM_BURST_WIDTH     {self.config['MEM_BURST_WIDTH']}\n"
        res += f"MEM_FREQ_KHZ:       {self.config['MEM_FREQ_KHZ']}\n"
        res += f"LATENCY_WIDTH:      {self.config['VALUE_WIDTH'][0]}\n"
        res += f"HIST_BOX_CNT:       {self.config['HIST_BOX_CNT'][0]}\n"
        res += f"HIST_BOX_WIDTH:     {self.config['HIST_BOX_WIDTH'][0]}\n"
        res += "\n"
        return res

    def print(self):
        print(self.config_to_str())

        stats = self.load_stats()
        print(self.stats_to_str(stats))


def parseParams():
    parser = argparse.ArgumentParser(
        description="mem_logger control script",
    )

    access = parser.add_argument_group('card access arguments')
    access.add_argument('-d', '--device', default=nfb.libnfb.Nfb.default_device,
                        metavar='device', help="""device with target FPGA card""")
    access.add_argument('-i', '--index', type=int, metavar='index', default=0, help="""index inside DevTree""")

    common = parser.add_argument_group('common arguments')
    #common.add_argument('-p', '--print', action='store_true', help = """print registers""")
    common.add_argument('--rst', action='store_true', help="""reset mem_tester and mem_logger""")
    args = parser.parse_args()
    return args


if __name__ == '__main__':
    args = parseParams()
    logger = MemLogger(dev=args.device, index=args.index)

    #if args.print:
    logger.print()

    if args.rst:
        logger.rst()

    #logger.set_config(latency_to_first=True)
