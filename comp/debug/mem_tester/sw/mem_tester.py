#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

import nfb
import time
import sys
import math
import argparse

from mem_logger.mem_logger import MemLogger


class MemTester(nfb.BaseComp):

    DT_COMPATIBLE = "netcope,mem_tester"

    # Mem_tester registers
    _REG_CTRL_IN             = 0x000000
    _REG_CTRL_OUT            = 0x000004
    _REG_ERR_CNT             = 0x000008
    _REG_BURST_CNT           = 0x00000C
    _REG_ADDR_LIM            = 0x000010
    _REG_REFRESH_PERIOD      = 0x000014
    _REG_DEF_REFRESH_PERIOD  = 0x000018

    # CTRL OUT BITS
    _BIT_TEST_DONE           = 0
    _BIT_TEST_SUCCESS        = 1
    _BIT_ECC_ERR             = 2
    _BIT_CALIB_SUCCESS       = 3
    _BIT_CALIB_FAIL          = 4
    _BIT_MAIN_AMM_READY      = 5

    # CTRL IN BITS
    _BIT_RESET               = 0
    _BIT_RESET_EMIF          = 1
    _BIT_RUN_TEST            = 2
    _BIT_AMM_GEN_EN          = 3
    _BIT_RANDOM_ADDR_EN      = 4
    _BIT_ONLY_ONE_SIMULT_READ = 5
    _BIT_AUTO_PRECHARGE_REQ  = 6

    # AMM_GEN registers
    AMM_GEN_BASE            = 0x00040
    _REG_AMM_GEN_CTRL        = AMM_GEN_BASE + 0x000000
    _REG_AMM_GEN_ADDR        = AMM_GEN_BASE + 0x000004
    _REG_AMM_GEN_SLICE       = AMM_GEN_BASE + 0x000008
    _REG_AMM_GEN_DATA        = AMM_GEN_BASE + 0x00000C
    _REG_AMM_GEN_BURST       = AMM_GEN_BASE + 0x000010

    # AMM_GEN CTRL REG bits
    _BIT_MEM_WR              = 0
    _BIT_MEM_RD              = 1
    _BIT_BUFF_VLD            = 2
    _BIT_AMM_READY           = 3

    def __init__(self, mem_logger, **kwargs):
        super().__init__(**kwargs)

        self.mem_logger = mem_logger
        self.last_test_config = None

    @staticmethod
    def compatible_cnt(dev=nfb.libnfb.Nfb.default_device, comp=None):
        dev = nfb.open(dev)
        nodes = dev.fdt_get_compatible(comp if comp is not None else MemTester.DT_COMPATIBLE)
        return len(nodes)

    def mi_toggle(self, addr, bit):
        self._comp.set_bit(addr, bit)
        self._comp.clr_bit(addr, bit)

    def mi_wait_bit(self, addr, bit, timeout=5, delay=0.01):
        t = 0
        while t < timeout:
            data = self._comp.read32(addr)
            if (data >> bit) & 1:
                return True
            else:
                t += delay
                time.sleep(delay)

        return False

    def load_status(self):
        status = {}

        ctrlo = self._comp.read32(self._REG_CTRL_OUT)
        status["test_done"]             = (ctrlo >> self._BIT_TEST_DONE)       & 1
        status["test_succ"]             = (ctrlo >> self._BIT_TEST_SUCCESS)    & 1
        status["ecc_err_occ"]           = (ctrlo >> self._BIT_ECC_ERR)         & 1
        status["calib_succ"]            = (ctrlo >> self._BIT_CALIB_SUCCESS)   & 1
        status["calib_fail"]            = (ctrlo >> self._BIT_CALIB_FAIL)      & 1
        status["amm_ready"]             = (ctrlo >> self._BIT_MAIN_AMM_READY)  & 1

        ctrli = self._comp.read32(self._REG_CTRL_IN)
        status["rst"]                   = (ctrli >> self._BIT_RESET)                 & 1
        status["rst_emif"]              = (ctrli >> self._BIT_RESET_EMIF)            & 1
        status["run_test"]              = (ctrli >> self._BIT_RUN_TEST)              & 1
        status["amm_gen_en"]            = (ctrli >> self._BIT_AMM_GEN_EN)            & 1
        status["random_addr_en"]        = (ctrli >> self._BIT_RANDOM_ADDR_EN)        & 1
        status["one_simult_read"]       = (ctrli >> self._BIT_ONLY_ONE_SIMULT_READ)  & 1
        status["auto_precharge"]        = (ctrli >> self._BIT_AUTO_PRECHARGE_REQ)    & 1

        status["err_cnt"]               = self._comp.read32(self._REG_ERR_CNT)
        status["burst_cnt"]             = self._comp.read32(self._REG_BURST_CNT)
        status["addr_lim"]              = self._comp.read32(self._REG_ADDR_LIM)
        status["refr_period_ticks"]     = self._comp.read32(self._REG_REFRESH_PERIOD)
        status["def_refr_period_ticks"] = self._comp.read32(self._REG_DEF_REFRESH_PERIOD)

        return status

    def status_to_str(self, status):
        res = ""
        res += "Mem_tester status:\n"
        res += "------------------\n"
        res += "control register:\n"
        res += "  -- output flags --\n"
        res += f"  test done                    {status['test_done']}\n"
        res += f"  test success                 {status['test_succ']}\n"
        res += f"  ecc error occurred           {status['ecc_err_occ']}\n"
        res += f"  calibration successful       {status['calib_succ']}\n"
        res += f"  calibration failed           {status['calib_fail']}\n"
        res += f"  memory ready                 {status['amm_ready']}\n"
        res += "  -- input flags --\n"
        res += f"  reset                        {status['rst']}\n"
        res += f"  reset memory controller      {status['rst_emif']}\n"
        res += f"  run test                     {status['run_test']}\n"
        res += f"  manual access                {status['amm_gen_en']}\n"
        res += f"  random addressing            {status['random_addr_en']}\n"
        res += f"  only one simultaneous read   {status['one_simult_read']}\n"
        res += f"  auto precharge               {status['auto_precharge']}\n"
        res += f"error count                    {status['err_cnt']}\n"
        res += f"burst count                    {status['burst_cnt']}\n"
        res += f"address limit                  {status['addr_lim']}\n"
        res += f"refresh period [ticks]         {status['refr_period_ticks']}\n"
        res += f"default refresh period [ticks] {status['def_refr_period_ticks']}\n"
        return res

    def rst(self, emif=True):
        self.mi_toggle(self._REG_CTRL_IN, self._BIT_RESET)
        if emif:
            self.mi_toggle(self._REG_CTRL_IN, self._BIT_RESET_EMIF)

        if not self._comp.wait_for_bit(self._REG_CTRL_OUT, self._BIT_MAIN_AMM_READY):
            print("Reset failed (MEM_READY was not set)", file=sys.stderr)
            return False
        return True

    def execute_test(self):
        self.mi_toggle(self._REG_CTRL_IN, self._BIT_RUN_TEST)
        if not self._comp.wait_for_bit(self._REG_CTRL_OUT, self._BIT_TEST_DONE, timeout=60):
            print("Test timeout (TEST_DONE was not set)", file=sys.stderr)

    def config_test(
        self,
        rand_addr=False,
        burst_cnt=4,
        addr_lim_scale=1.0,
        only_one_simult_read=False,
        latency_to_first=False,
        auto_precharge=False,
        refresh_period=None,
    ):
        if burst_cnt > 2 ** self.mem_logger.config["MEM_BURST_WIDTH"] - 1:
            print(f"Burst count {burst_cnt} is too large", file=sys.stderr)
            return

        self.rst(False)
        self.mem_logger.rst()
        self._comp.write32(self._REG_BURST_CNT, burst_cnt)

        ctrli = 0
        if rand_addr:
            ctrli += (1 << self._BIT_RANDOM_ADDR_EN)
        if only_one_simult_read:
            ctrli += (1 << self._BIT_ONLY_ONE_SIMULT_READ)
        if auto_precharge:
            ctrli += (1 << self._BIT_AUTO_PRECHARGE_REQ)
        self._comp.write32(self._REG_CTRL_IN, ctrli)

        addr_lim = 0
        max_addr = 2 ** self.mem_logger.config["MEM_ADDR_WIDTH"] * addr_lim_scale
        if addr_lim_scale >= 1.0:
            max_addr -= 2 * burst_cnt
        addr_lim = int((max_addr // burst_cnt) * burst_cnt)
        self._comp.write32(self._REG_ADDR_LIM, addr_lim)

        if latency_to_first:
            self.mem_logger.set_config(latency_to_first=True)

        if refresh_period is None:
            refresh_period = self.load_status()["def_refr_period_ticks"]
        self._comp.write32(self._REG_REFRESH_PERIOD, refresh_period)

        self.last_test_config = {
            "rand_addr":            rand_addr,
            "burst_cnt":            burst_cnt,
            "addr_lim_scale":       addr_lim_scale,
            "only_one_simult_read": only_one_simult_read,
            "latency_to_first":     latency_to_first,
            "auto_precharge":       auto_precharge,
            "refresh_period":       refresh_period,
        }

    def check_test_result(self, config, status, stats):
        errs = ""
        if status["err_cnt"] != 0 and not config["rand_addr"]:
            errs += f"{status['err_cnt']} words were wrong\n"
        if status["ecc_err_occ"]:
            errs += "ECC error occurred\n"
        if stats["rd_req_words"] != stats["rd_resp_words"]:
            errs += f"{stats['rd_req_words'] - stats['rd_resp_words']} words were not received\n"
        if not status["test_succ"] and errs == "" and not config["rand_addr"]:
            errs += "Unknown error occurred\n"
        return errs

    def get_test_result(self):
        config = self.last_test_config
        status = self.load_status()
        stats = self.mem_logger.load_stats()
        errs = self.check_test_result(config, status, stats)
        return config, status, stats, errs

    def test_result_to_str(self, config, status, stats, errs):
        res = ""
        if errs == "":
            res += "|| ------------------- ||\n"
            res += "|| TEST WAS SUCCESSFUL ||\n"
            res += "|| ------------------- ||\n"
        else:
            res += "|| ----------- ||\n"
            res += "|| TEST FAILED ||\n"
            res += "|| ----------- ||\n"
            res += "\nErrors:\n"
            res += errs
        res += "\n"
        res += self.mem_logger.stats_to_str(stats)
        return res

    def amm_gen_set_buff(self, burst, data):
        prev_addr = self._comp.read32(self._REG_AMM_GEN_ADDR)
        mi_width  = self.mem_logger.config["MI_DATA_WIDTH"]
        slices    = math.ceil(self.mem_logger.config["MEM_DATA_WIDTH"] / mi_width)

        for s in range(0, slices):
            slice = self.mem_logger.get_bits(data, mi_width, mi_width * s)
            self._comp.write32(self._REG_AMM_GEN_ADDR, burst)
            self._comp.write32(self._REG_AMM_GEN_SLICE, s)
            self._comp.write32(self._REG_AMM_GEN_DATA, slice)

        self._comp.write32(self._REG_AMM_GEN_ADDR, prev_addr)

    def amm_gen_get_buff(self):
        mi_width  = self.mem_logger.config["MI_DATA_WIDTH"]
        slices    = math.ceil(self.mem_logger.config["MEM_DATA_WIDTH"] / mi_width)
        prev_addr = self._comp.read32(self._REG_AMM_GEN_ADDR)
        burst     = self._comp.read32(self._REG_AMM_GEN_BURST)

        data = []
        for b in range(0, burst):
            val = 0
            for s in range(0, slices):
                self._comp.write32(self._REG_AMM_GEN_ADDR, b)
                self._comp.write32(self._REG_AMM_GEN_SLICE, s)
                slice = self._comp.read32(self._REG_AMM_GEN_DATA)
                val += slice << (s * mi_width)
            data.append(val)

        self._comp.write32(self._REG_AMM_GEN_ADDR, prev_addr)
        return data

    def amm_gen_set_burst(self, burst):
        self._comp.write32(self._REG_AMM_GEN_BURST, burst)

    def amm_gen_write(self, addr):
        self._comp.write32(self._REG_AMM_GEN_ADDR, addr)
        self._comp.set_bit(self._REG_CTRL_IN, self._BIT_AMM_GEN_EN)
        self.mi_toggle(self._REG_AMM_GEN_CTRL, self._BIT_MEM_WR)
        self._comp.clr_bit(self._REG_CTRL_IN, self._BIT_AMM_GEN_EN)

    def amm_gen_read(self, addr):
        self._comp.write32(self._REG_AMM_GEN_ADDR, addr)
        self._comp.set_bit(self._REG_CTRL_IN, self._BIT_AMM_GEN_EN)
        self.mi_toggle(self._REG_AMM_GEN_CTRL, self._BIT_MEM_RD)
        self._comp.clr_bit(self._REG_CTRL_IN, self._BIT_AMM_GEN_EN)

    def amm_gen_to_str(self):
        ctrl  = self._comp.read32(self._REG_AMM_GEN_CTRL)
        addr  = self._comp.read32(self._REG_AMM_GEN_ADDR)
        slice = self._comp.read32(self._REG_AMM_GEN_SLICE)
        burst = self._comp.read32(self._REG_AMM_GEN_BURST)
        data  = self._comp.read32(self._REG_AMM_GEN_DATA)

        res = "Amm_gen status:\n"
        res += "--------------\n"
        res += "control register:\n"
        res += f"  memory write                 {(ctrl >> self._BIT_MEM_WR) & 1}\n"
        res += f"  memory read                  {(ctrl >> self._BIT_MEM_RD) & 1}\n"
        res += f"  buffer vld                   {(ctrl >> self._BIT_BUFF_VLD) & 1}\n"
        res += f"  memory ready                 {(ctrl >> self._BIT_AMM_READY) & 1}\n"
        res += f"address                        {addr}\n"
        res += f"slice                          {slice}\n"
        res += f"burst                          {burst}\n"
        res += f"data                           {data}\n"
        return res


def parseParams():
    parser = argparse.ArgumentParser(
        description="mem_tester control script",
        #formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )

    access = parser.add_argument_group('card access arguments')
    access.add_argument('-d', '--device', default=nfb.libnfb.Nfb.default_device,
                        metavar='device', help="""device with target FPGA card.""")
    access.add_argument('-i', '--index',        type=int, metavar='index', default=0, help="""mem_tester index inside DevTree.""")
    access.add_argument('-I', '--logger-index', type=int, metavar='index', default=None, help="""mem_logger index inside DevTree.""")

    common = parser.add_argument_group('common arguments')
    common.add_argument('-p', '--print', action='store_true', help="""print registers""")
    common.add_argument('--rst', action='store_true', help="""reset mem_tester and mem_logger""")
    common.add_argument('--rst-tester', action='store_true', help="""reset mem_tester""")
    common.add_argument('--rst-logger', action='store_true', help="""reset mem_logger""")
    common.add_argument('--rst-emif',   action='store_true', help="""reset memory driver""")

    test = parser.add_argument_group('test related arguments')
    #test.add_argument('-t', '--test', action='store_true', help = """run test""")
    test.add_argument('-r', '--rand', action='store_true', help="""use random indexing during test""")
    test.add_argument('-b', '--burst', default=4, type=int, help="""burst count during test""")
    test.add_argument('-s', '--scale', default=1.0, type=float, help="""tested address space (1.0 = whole)""")
    test.add_argument('-o', '--one-simult', action='store_true', help="""use only one simultaneous read during test""")
    test.add_argument('-f', '--to-first', action='store_true', help="""measure latency to the first received word""")
    test.add_argument('--auto-precharge',  action='store_true', help="""use auto precharge during test""")
    test.add_argument('--refresh', default=None, type=int, help="""set refresh period in ticks""")

    other = parser.add_argument_group('amm_gen control arguments')
    other.add_argument('--set-buff', metavar=('burst', 'data'), type=int, nargs=2, help="""set specific burst data in amm_gen buffer""")
    other.add_argument('--get-buff', action='store_true', help="""print amm_gen buffer""")
    other.add_argument('--gen-wr', metavar='addr', type=int, help="""writes amm_gen buffer to specific address""")
    other.add_argument('--gen-rd', metavar='addr', type=int, help="""reads memory data to amm_gen buffer""")
    other.add_argument('--gen-burst', type=int, help="""sets burst count for amm_gen""")

    args = parser.parse_args()
    return args


if __name__ == '__main__':
    args = parseParams()

    if args.logger_index is None:
        args.logger_index = args.index

    logger = MemLogger(dev=args.device, index=args.logger_index)
    tester = MemTester(logger, dev=args.device, index=args.index)

    if args.print:
        status = tester.load_status()
        print(tester.status_to_str(status))
        print(tester.mem_logger.config_to_str())
        stats = tester.mem_logger.load_stats()
        print(tester.mem_logger.stats_to_str(stats))
        print(tester.amm_gen_to_str())

    elif args.rst or args.rst_tester:
        tester.rst(False)
    elif args.rst or args.rst_logger:
        tester.mem_logger.rst()
    elif args.rst_emif:
        tester.rst(True)

    elif args.gen_burst is not None:
        tester.amm_gen_set_burst(args.gen_burst)
    elif args.gen_wr is not None:
        print(f"Writing to address {args.gen_wr}")
        tester.amm_gen_write(args.gen_wr)
    elif args.gen_rd is not None:
        print(f"Reading from address {args.gen_rd}")
        tester.amm_gen_read(args.gen_rd)
    elif args.set_buff is not None:
        tester.amm_gen_set_buff(args.set_buff[0], args.set_buff[1])
    elif args.get_buff or args.gen_rd is not None:
        buff = tester.amm_gen_get_buff()
        for i, b in enumerate(buff):
            print(f"{i:>4}: {b}")

    else:
        tester.config_test(
            args.rand,
            args.burst,
            args.scale,
            args.one_simult,
            args.to_first,
            args.auto_precharge,
            args.refresh,
        )
        tester.execute_test()
        config, status, stats, errs = tester.get_test_result()
        print(tester.test_result_to_str(config, status, stats, errs))
