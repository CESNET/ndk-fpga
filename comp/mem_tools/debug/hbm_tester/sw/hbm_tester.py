#!/usr/bin/env python3
# Copyright (C) 2024 CESNET
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import nfb
import time
import math
import argparse


class hbm_tester:
    DT_COMPATIBLE = "cesnet,ofm,hbm_tester"

    _REG_RESET     = 0x018
    _REG_CONFIG    = 0x014
    _REG_TIME      = 0x01C
    _REG_RUN_TEST  = 0x010
    _REG_DONE_TEST = 0x020
    _REG_STAT_BASE = 0x200

    _CONF_DISABLED     = 0x0
    _CONF_GEN_EN       = 0x1
    _CONF_RAND_ADDR_EN = 0x2
    _CONF_WR_DEAD_EN   = 0x4
    _CONF_RW_SWITCH_EN = 0x8
    _CONF_BL8_MODE     = 0x40
    _CONF_RW_NO_WAIT   = 0x80

    _GEN_CONF_WR_ONLY = (0x1 + 0x0) * 0x10
    _GEN_CONF_RD_ONLY = (0x2 + 0x0) * 0x10
    _GEN_CONF_WR_RD   = (0x3 + 0x0) * 0x10

    # Throughput tests, they differ only in the direction the generator drives.
    _SPEED_TESTS = ("speed", "speed-rd", "speed-wr")

    _MON_CONF_SPEED_TEST   = 0x10 * 0x100 # counter0 = RD words, counter1 = WR words
    _MON_CONF_LATENCY_TEST = 0x32 * 0x100 # counter0 = RD latency, counter1 = WR latency
    _MON_CONF_DATA_TEST    = 0x54 * 0x100 # counter0 = data OK, counter1 = dat ERROR

    def __init__(self, dev, index, ports=32, width=256, freq=450.0):
        self.node = dev.fdt_get_compatible(self.DT_COMPATIBLE)[index]
        self.comp = dev.comp_open(self.node)
        self.ports = ports
        self.width = width
        self.clk_period = (1 / (freq * 1e6)) * 1e9
        self.rw_no_wait = False

    def reset_all_counters(self):
        self.comp.write32(self._REG_RESET, self.get_ports_vector(self.ports))
        time.sleep(0.1)
        self.comp.write32(self._REG_RESET, 0x0)

    def set_test_length(self, test_length):
        #print("REG_TIME: %s" % hex(test_length))
        self.comp.write32(self._REG_TIME, test_length)

    def check_bl_mode(self):
        # BL4 is a 32B access, so it needs a data bus
        # of at most 32B. On a wider bus one word already carries more than that and
        # the tester falls back to the 64B access of BL8.
        conf_data = self.comp.read32(self._REG_CONFIG)
        bl4_set   = (conf_data & self._CONF_BL8_MODE) == 0

        if bl4_set and self.width > 256:
            print("WARNING: HBM_TESTER: BL4 mode cannot generate its 32B access on a %db "
                  "data bus, the tester issues the 64B of BL8 instead." % self.width)

    def get_bl_mode_string(self, bl8):
        if bl8 is True:
            return "BL8"
        else:
            return "BL4"

    def set_config_reg(self, test_type, test_phase, rand_addr, bl8=False):
        if rand_addr is True:
            rand_test_val = self._CONF_RAND_ADDR_EN
        else:
            rand_test_val = self._CONF_DISABLED

        if test_type == "none":
            conn_gen_val  = self._CONF_DISABLED
            dead_wr_val   = self._CONF_DISABLED
            switch_rw_val = self._CONF_DISABLED
            gen_conf_val  = self._GEN_CONF_WR_RD
            mon_conf_val  = self._MON_CONF_SPEED_TEST
        elif test_type in self._SPEED_TESTS:
            conn_gen_val  = self._CONF_GEN_EN
            dead_wr_val   = self._CONF_DISABLED
            switch_rw_val = self._CONF_DISABLED
            mon_conf_val  = self._MON_CONF_SPEED_TEST
            if test_type == "speed-rd":
                gen_conf_val = self._GEN_CONF_RD_ONLY
            elif test_type == "speed-wr":
                gen_conf_val = self._GEN_CONF_WR_ONLY
            else:
                gen_conf_val = self._GEN_CONF_WR_RD
        elif test_type == "latency":
            conn_gen_val  = self._CONF_GEN_EN
            dead_wr_val   = self._CONF_DISABLED
            switch_rw_val = self._CONF_DISABLED
            gen_conf_val  = self._GEN_CONF_WR_RD
            mon_conf_val  = self._MON_CONF_LATENCY_TEST
        elif test_type == "integrity":
            conn_gen_val  = self._CONF_GEN_EN
            dead_wr_val   = self._CONF_DISABLED
            switch_rw_val = self._CONF_DISABLED
            rand_test_val = self._CONF_DISABLED
            gen_conf_val  = self._GEN_CONF_WR_ONLY
            mon_conf_val  = self._MON_CONF_DATA_TEST
            if test_phase == 1:
                gen_conf_val = self._GEN_CONF_RD_ONLY
        elif test_type == "coherency":
            conn_gen_val  = self._CONF_GEN_EN
            dead_wr_val   = self._CONF_WR_DEAD_EN
            switch_rw_val = self._CONF_DISABLED
            rand_test_val = self._CONF_DISABLED
            gen_conf_val  = self._GEN_CONF_WR_ONLY
            mon_conf_val  = self._MON_CONF_DATA_TEST
            if test_phase == 1:
                dead_wr_val   = self._CONF_DISABLED
                switch_rw_val = self._CONF_RW_SWITCH_EN
                gen_conf_val  = self._GEN_CONF_WR_RD

        conf_data = rand_test_val + dead_wr_val + switch_rw_val + gen_conf_val + mon_conf_val + conn_gen_val
        if self.rw_no_wait:
            conf_data += self._CONF_RW_NO_WAIT
        if bl8:
            conf_data += self._CONF_BL8_MODE
        #print("REG_CONFIG: %s" % hex(conf_data))
        self.comp.write32(self._REG_CONFIG, conf_data)
        self.check_bl_mode()

    def get_ports_vector(self, hbm_ports):
        return int(math.pow(2, hbm_ports) - 1)

    def get_counter(self, counter, hbm_port):
        reg_addr = self._REG_STAT_BASE + (hbm_port * 0x10) + (counter * 0x4)
        #print("HBM PORT: %d" % hbm_port)
        #print("COUNTER:  %d" % counter)
        #print("REG_ADDR: %s" % hex(reg_addr))
        return self.comp.read32(reg_addr)

    def get_speed(self, counter, hbm_port, test_time):
        data_words = self.get_counter(counter, hbm_port)
        bits = data_words * self.width
        speed = bits / test_time
        #print("words:     %d" % data_words)
        #print("bits:      %d" % bits)
        #print("test_time: %f" % test_time)
        #print("speed:     %.2f Gbps" % speed)
        return speed

    def print_speed_result(self, test_length, hbm_ports):
        #print("test_length: %d" % test_length)
        #print("clk_period:  %f" % self.clk_period)
        test_time = test_length * self.clk_period
        rd_speed_total = 0
        wr_speed_total = 0

        for ii in range(0, hbm_ports):
            print("HBM PORT: %d" % ii)
            print("---------------------------")
            speed = self.get_speed(0, ii, test_time)
            rd_speed_total += speed
            print("Read speed:   %.2f Gbps" % speed)
            speed = self.get_speed(1, ii, test_time)
            wr_speed_total += speed
            print("Write speed:  %.2f Gbps" % speed)
            print("---------------------------")

        print("HBM TOTAL READ SPEED:  %.2f Gbps" % rd_speed_total)
        print("HBM TOTAL WRITE SPEED: %.2f Gbps" % wr_speed_total)

        # Return speeds so they can be summed globally
        return rd_speed_total, wr_speed_total

    def print_latency_result(self, hbm_ports):
        for ii in range(0, hbm_ports):
            print("HBM PORT: %d" % ii)
            print("---------------------------")
            latency = self.get_counter(0, ii)
            latency_ns = latency * self.clk_period
            print("RD latency: %d clk cycles (%.2f ns)" % (latency, latency_ns))
            latency = self.get_counter(1, ii)
            latency_ns = latency * self.clk_period
            print("WR latency: %d clk cycles (%.2f ns)" % (latency, latency_ns))
            print("---------------------------")

    def print_data_result(self, hbm_ports):
        for ii in range(0, hbm_ports):
            print("HBM PORT: %d" % ii)
            print("---------------------------")
            words = self.get_counter(0, ii)
            print("Valid words: %d" % words)
            words = self.get_counter(1, ii)
            print("Error words: %d" % words)
            print("---------------------------")

    def run_test(self, hbm_ports):
        ports_vector = self.get_ports_vector(hbm_ports)
        test_done = False
        ii = 0
        #print("REG_RUN_TEST: %s" % hex(ports_vector))
        self.comp.write32(self._REG_RUN_TEST, ports_vector)

        while test_done is False:
            time.sleep(0.1)
            reg_done = self.comp.read32(self._REG_DONE_TEST)
            #print("REG_DONE_TEST: %s" % hex(reg_done))
            test_done = (reg_done == ports_vector)
            ii += 1
            if ii > 5:
                print("HBM test iteration: " + str(ii))
            if ii > 10:
                print("HBM test done fail!")
                break

        self.comp.write32(self._REG_RUN_TEST, 0x0)
        time.sleep(0.1)

    def get_addr_mode_string(self, rand_addr):
        if rand_addr is True:
            return "pseudorandom"
        else:
            return "sequential"

    def hbm_test(self, test_type, rand_addr, hbm_ports, test_length, bl8=False):
        print("===========================")
        print("HBM TESTER by CESNET")
        print("===========================")
        print("TEST TYPE:   " + str(test_type))
        print("TEST LENGTH: " + hex(test_length))
        print("ADDR MODE:   " + str(self.get_addr_mode_string(rand_addr)))
        print("BURST MODE:  " + str(self.get_bl_mode_string(bl8)))
        print("USED PORTS:  " + str(hbm_ports))
        print("===========================")

        self.reset_all_counters()
        if (test_type == "integrity") or (test_type == "coherency"):
            self.set_test_length(0xFFFF)
        else:
            self.set_test_length(test_length)
        self.set_config_reg(test_type, 0, rand_addr, bl8)
        self.run_test(hbm_ports)

        # Track speeds for the return value
        rd_speed, wr_speed = 0.0, 0.0

        if test_type in self._SPEED_TESTS:
            rd_speed, wr_speed = self.print_speed_result(test_length, hbm_ports)
        elif test_type == "latency":
            self.print_latency_result(hbm_ports)
        elif (test_type == "integrity") or (test_type == "coherency"):
            #self.print_data_result(hbm_ports)
            self.reset_all_counters()
            self.set_test_length(0xEFFF)
            self.set_config_reg(test_type, 1, rand_addr, bl8)
            self.run_test(hbm_ports)
            self.print_data_result(hbm_ports)

        return rd_speed, wr_speed


if __name__ == '__main__':
    # Argument parsing
    args = argparse.ArgumentParser()
    args.add_argument("-i", "--index", action="store", default='all', help="Index of the HBM tester (e.g., 0 or 1), or 'all' to run on both.")
    args.add_argument("-d", "--device", action="store", default='0')
    args.add_argument("-t", "--test", action="store", choices=['speed', 'speed-rd', 'speed-wr', 'latency', 'integrity', 'coherency'], default='speed')
    args.add_argument("-r", "--random", action='store_true', help="Use random addressing (only for latency or speed test), default is sequential.")
    args.add_argument("-w", "--no-wait", action='store_true', help="Do not wait for the write response before reading the same address (coherency test).")
    args.add_argument("-b", "--bl8", action='store_true', help="Use the BL8 burst mode (64B access), default is BL4 (32B access).")
    args.add_argument("-p", "--ports", action="store", nargs='?', default='0', help="Number of actived ports (channels), default is all.")
    args.add_argument("-P", "--tester-ports", type=int, default=32, help="Number of ports of one tester instance (HBM_PORTS/HBM_MODULES), default 32.")
    args.add_argument("-W", "--data-width", type=int, choices=[256, 512], default=256, help="HBM_DATA_WIDTH of the build, default 256.")
    args.add_argument("-F", "--freq", type=float, default=450.0, help="HBM_CLK frequency in MHz, default 450.")
    #args.add_argument("-l","--length", action="store", nargs='?', default='0xFFFFFF', help="Length of test in clock cycles (only for latency or speed test), default is 0xFFFFFF.")
    arguments = args.parse_args()

    # Open nfb device
    dev = nfb.open(arguments.device)

    # Count how many compatible nodes exist in the device tree
    compatible_nodes = dev.fdt_get_compatible(hbm_tester.DT_COMPATIBLE)
    node_count = len(compatible_nodes)

    if node_count == 0:
        print(f"Error: No '{hbm_tester.DT_COMPATIBLE}' nodes found in the device tree.")
        exit(1)

    # Determine which indices to test
    indices_to_test = []
    if arguments.index.lower() == 'all':
        indices_to_test = list(range(node_count))
    else:
        idx = int(arguments.index, 0)
        if idx >= node_count:
            print(f"Error: Index {idx} is out of bounds. Found {node_count} testers.")
            exit(1)
        indices_to_test = [idx]

    # Initialize variables to keep track of the grand total
    grand_total_rd_speed = 0.0
    grand_total_wr_speed = 0.0

    # Run tests on selected instances
    for idx in indices_to_test:
        print(f"\n>>> Initializing HBM Tester [Index {idx}] <<<")
        tester = hbm_tester(dev, idx, ports=arguments.tester_ports, width=arguments.data_width, freq=arguments.freq)
        tester.rw_no_wait = arguments.no_wait

        arg_ports = int(arguments.ports, 0)
        if arg_ports == 0:
            arg_ports = tester.ports

        arg_length = 0xFFFFF

        # Capture the returned speeds from each tester instance
        rd, wr = tester.hbm_test(arguments.test, arguments.random, arg_ports, arg_length, arguments.bl8)

        if arguments.test in hbm_tester._SPEED_TESTS:
            grand_total_rd_speed += rd
            grand_total_wr_speed += wr

    # Print the grand total if we ran a speed test on more than one tester
    if arguments.test in hbm_tester._SPEED_TESTS and len(indices_to_test) > 1:
        print("\n=================================================")
        print("OVERALL HBM SPEED TOTALS (ALL TESTERS)")
        print("=================================================")
        print("GRAND TOTAL READ SPEED:  %.2f Gbps" % grand_total_rd_speed)
        print("GRAND TOTAL WRITE SPEED: %.2f Gbps" % grand_total_wr_speed)
        print("=================================================\n")
