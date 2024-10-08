# test_fifo_bram : testbench file
# Copyright (C) 2021 CESNET
# Author: Daniel Kriz <xkrizd01@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import cocotb
from cocotb.triggers import Timer
import random
from queue import Queue
from cocotb.triggers import FallingEdge
from cocotb.triggers import RisingEdge


#Clock generator
@cocotb.coroutine
def clock_gen(clk, period=10):
    while True:
        clk.value = 0
        yield Timer(period / 2, units='ns')
        clk.value = 1
        yield Timer(period / 2, units='ns')


@cocotb.test()
async def fifo_bram_randomised_test(dut):
    NUMBER_OF_TRANSACTIONS = 10
    PERIOD = 10
    # ITEMS = 1024
    clkedgeF = FallingEdge(dut.CLK)
    clkedgeR = RisingEdge(dut.CLK)

    #clk = dut.CLK
    #reset = dut.RESET
    write = 0
    data_in = 0
    #data_out = 0
    read = 0
    data_stream = Queue(maxsize=0)

    cocotb.fork(clock_gen(dut.CLK, PERIOD))

    #Reset of design
    dut.RESET <= 1
    dut.RD <= read
    dut.WR <= write
    dut.DI <= data_in

    await clkedgeR
    dut.RESET <= 0
    await clkedgeF

    ver_done = 0
    cnt_write = 0
    cnt_read = 0
    write_allow = 1

    while ver_done == 0:
        data_in = random.randint(0, dut.DATA_WIDTH.value)
        write = random.choice([True, False])
        read  = random.choice([True, False])

        dut.RD <= read
        dut.WR <= write
        dut.DI <= data_in

        if write == 1 and dut.FULL.value == 0 and write_allow == 1:
            data_stream.put(data_in)
            cnt_write += 1
            print("DI: ")
            print(data_in)

        if dut.DV.value == 1 and read == 1:
            data_out = data_stream.get()
            print("DO: ")
            print(dut.DO.value.integer)
            print(data_out)
            assert dut.DO.value == data_out, "Randomised test failed with: {A} and {B}".format(
                A=dut.DO.value.integer, B=data_out)
            cnt_read += 1
            #ver_done = 1

        await clkedgeF

        if cnt_write == NUMBER_OF_TRANSACTIONS:
            write_allow = 0
            #ver_done = 1

        if cnt_read == NUMBER_OF_TRANSACTIONS and write_allow == 0:
            ver_done = 1
            print("Verification finished successfully")
            print("FIFO is empty")
