#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

from mem_tester import MemTester
from mem_logger.mem_logger import MemLogger

# python3 -m pytest -xs --tb=short test_mem_tester.py
# -s ... to show measured data
# -x ... end after first failure
# -tb ... show only assertion message

#########
# TESTS #
#########

device = '/dev/nfb0'


def comp_cnt(comp=MemTester.DT_COMPATIBLE):
    return MemTester.compatible_cnt(comp=comp, dev=device)


def test_comp_cnt():
    tester_cnt = comp_cnt()
    assert tester_cnt > 0, "No mem_tester found"

    logger_cnt = comp_cnt(comp='netcope,mem_logger')  # todo
    assert logger_cnt > 0, "No mem_logger found"

    assert logger_cnt == tester_cnt, "Number of mem_testers does not match number of mem_loggers"


def open(index):
    logger = MemLogger(index=index, dev=device)
    tester = MemTester(logger, index=index, dev=device)
    return tester


def test_open():
    for i in range(0, comp_cnt()):
        open(i)


def test_status():
    for i in range(0, comp_cnt()):
        tester = open(i)
        status = tester.load_status()

        assert status["calib_succ"] or status["calib_fail"], "Memory calibration was not finished"
        assert status["calib_succ"], "Memory calibration was not successful"
        assert status["amm_ready"], "Memory is not ready"


def test_config():
    for i in range(0, comp_cnt()):
        tester = open(i)
        config = tester.mem_logger.config

        assert config["MEM_DATA_WIDTH"]     > 0, f"Invalid MEM_DATA_WIDTH    ({config['MEM_DATA_WIDTH']})"
        assert config["MEM_ADDR_WIDTH"]     > 0, f"Invalid MEM_ADDR_WIDTH    ({config['MEM_ADDR_WIDTH']})"
        assert config["MEM_BURST_WIDTH"]    > 0, f"Invalid MEM_BURST_WIDTH   ({config['MEM_BURST_WIDTH']})"
        assert config["MEM_FREQ_KHZ"]       > 0, f"Invalid MEM_FREQ_KHZ      ({config['MEM_FREQ_KHZ']})"


def test_seq():
    for i in range(0, comp_cnt()):
        tester = open(i)
        min_burst = 1
        max_burst = 2 ** tester.mem_logger.config["MEM_BURST_WIDTH"] - 1

        for b in (min_burst, max_burst):
            print()
            print(f"Memory interface {i}, burst count {b}")

            tester.config_test(burst_cnt=b)
            tester.execute_test()
            config, status, stats, errs = tester.get_test_result()

            print(tester.test_result_to_str(config, status, stats, errs))
            assert errs == '', f"Errors occurred during test:\n {errs}"
            assert stats['wr_req_cnt'] > 0, "No write requests were send"
            assert stats['rd_req_cnt'] > 0, "No read requests were send"
            #assert stats['latency']['max_ns'] < 2000, "Too large maximum latency"
            #if b == min_burst:
            #    assert stats['latency']['avg_ns'] < 500, "Too large average latency"

    test_status()
