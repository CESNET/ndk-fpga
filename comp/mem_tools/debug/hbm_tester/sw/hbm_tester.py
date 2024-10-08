#!/usr/bin/python3
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

    _GEN_CONF_WR_ONLY = (0x1 + 0x0) * 0x10
    _GEN_CONF_RD_ONLY = (0x2 + 0x0) * 0x10
    _GEN_CONF_WR_RD   = (0x3 + 0x0) * 0x10

    _MON_CONF_SPEED_TEST   = 0x10 * 0x100 # counter0 = RD words, counter1 = WR words
    _MON_CONF_LATENCY_TEST = 0x32 * 0x100 # counter0 = RD latency, counter1 = WR latency
    _MON_CONF_DATA_TEST    = 0x54 * 0x100 # counter0 = data OK, counter1 = dat ERROR

    def __init__(self, dev, index):
        self.node = dev.fdt_get_compatible(self.DT_COMPATIBLE)[index]
        self.comp = dev.comp_open(self.node)
        self.ports = 32 # TODO register
        self.width = 256 # TODO register
        self.clk_period = (1 / 450000000) * 1e9 # TODO register

    def reset_all_counters(self):
        self.comp.write32(self._REG_RESET, self.get_ports_vector(self.ports))
        time.sleep(0.1)
        self.comp.write32(self._REG_RESET, 0x0)

    def set_test_length(self, test_length):
        #print("REG_TIME: %s" % hex(test_length))
        self.comp.write32(self._REG_TIME, test_length)

    def set_config_reg(self, test_type, test_phase, rand_addr):
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
        elif test_type == "speed":
            conn_gen_val  = self._CONF_GEN_EN
            dead_wr_val   = self._CONF_DISABLED
            switch_rw_val = self._CONF_DISABLED
            gen_conf_val  = self._GEN_CONF_WR_RD
            mon_conf_val  = self._MON_CONF_SPEED_TEST
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
        #print("REG_CONFIG: %s" % hex(conf_data))
        self.comp.write32(self._REG_CONFIG, conf_data)

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

    def hbm_test(self, test_type, rand_addr, hbm_ports, test_length):
        print("===========================")
        print("HBM TESTER by CESNET")
        print("===========================")
        print("TEST TYPE:   " + str(test_type))
        print("TEST LENGTH: " + hex(test_length))
        print("ADDR MODE:   " + str(self.get_addr_mode_string(rand_addr)))
        print("USED PORTS:  " + str(hbm_ports))
        print("===========================")

        self.reset_all_counters()
        if (test_type == "integrity") or (test_type == "coherency"):
            self.set_test_length(0xFFFF)
        else:
            self.set_test_length(test_length)
        self.set_config_reg(test_type, 0, rand_addr)
        self.run_test(hbm_ports)

        if test_type == "speed":
            self.print_speed_result(test_length, hbm_ports)
        elif test_type == "latency":
            self.print_latency_result(hbm_ports)
        elif (test_type == "integrity") or (test_type == "coherency"):
            #self.print_data_result(hbm_ports)
            self.reset_all_counters()
            self.set_test_length(0xEFFF)
            self.set_config_reg(test_type, 1, rand_addr)
            self.run_test(hbm_ports)
            self.print_data_result(hbm_ports)


if __name__ == '__main__':
    # Argument parsing
    args = argparse.ArgumentParser()
    args.add_argument("-i", "--index", action="store", nargs='?', default='0')
    args.add_argument("-d", "--device", action="store", nargs='?', default='0')
    args.add_argument("-t", "--test", action="store", nargs='?', choices=['speed', 'latency', 'integrity', 'coherency'], default='speed')
    args.add_argument("-r", "--random", action='store_true', help="Use random addressing (only for latency or speed test), default is sequential.")
    args.add_argument("-p", "--ports", action="store", nargs='?', default='0', help="Number of actived ports (channels), default is all.")
    #args.add_argument("-l","--length", action="store", nargs='?', default='0xFFFFFF', help="Length of test in clock cycles (only for latency or speed test), default is 0xFFFFFF.")
    arguments = args.parse_args()

    # Open nfb device
    dev = nfb.open(arguments.device)

    tester = hbm_tester(dev, int(arguments.index[0], 0))

    arg_ports = int(arguments.ports[0], 0)
    if arg_ports == 0:
        arg_ports = tester.ports
    arg_length = 0xFFFFF # int(arguments.length[0], 0)

    tester.hbm_test(arguments.test, arguments.random, arg_ports, arg_length)
    # reset config register after test
    #tester.set_config_reg("none", 0, False)
