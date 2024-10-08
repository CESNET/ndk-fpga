#!/usr/bin/env python

# cocotb_test.py: MVB_HASH_TABLE_SIMPLE component test
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""
This test requires a configuration file to function.
You could either choose one of the prepared ones in the
'test_configs' directory or create your own via configuration
script in the 'sw' directory and running it with -i (interactive)
argument.
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.mi.drivers import MIMasterDriver as MIDriver
from drivers import MVB_HASH_TABLE_SIMPLE_Driver as MVBDriver
from monitors import MVB_HASH_TABLE_SIMPLE_Monitor as MVBMonitor
from cocotbext.ofm.ver.generators import random_packets
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard

import nfb
from sw.toolkit import MVB_HASH_TABLE_SIMPLE_TOOLKIT, toeplitz_hash, simple_xor_hash
from cocotbext.ofm.utils.servicer import Servicer
from cocotbext.ofm.utils.device import get_dtb
from cocotbext.ofm.utils.math import ceildiv

import itertools
from math import log2
import yaml

# MI ADDRESS SPACE
_COMMAND_REG    = 0x00
_ADDR_REG       = 0x04
_DATA_REG       = 0x08
_COMMIT_REG     = 0x0C
_HASH_KEY_REG   = 0x10
# COMMAND REGISTER COMMANDS
_CHOOSE_TAB0    = 0x00
_CHOOSE_TAB1    = 0x01
_CLEAR_TABLES   = 0x02
# Read interface commands and returned data
_MVB_ITEMS      = 0x00
_MVB_KEY_WIDTH  = 0x04
_DATA_OUT_WIDTH = 0x08
_HASH_WIDTH     = 0x0C
_HASH_KEY_WIDTH = 0x10
_TABLE_CAPACITY = 0x14


class testbench():
    def __init__(self, dut, debug=False) -> None:
        self.dut = dut
        self.stream_in = MVBDriver(dut, "RX_MVB", dut.CLK)
        self.backpressure = BitDriver(dut.TX_MVB_DST_RDY, dut.CLK)
        self.stream_out = MVBMonitor(dut, "TX_MVB", dut.CLK)
        self.mi_interface = MIDriver(dut, "MI", dut.CLK)

        self.stream_out.bus.dst_rdy.value = 1

        # Create a scoreboard on the stream_out bus
        self.pkts_sent = 0
        self.expected_output = []
        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.stream_out, self.expected_output)

        if debug:
            self.stream_in.log.setLevel(cocotb.logging.DEBUG)
            self.stream_out.log.setLevel(cocotb.logging.DEBUG)
            self.mi_interface.log.setLevel(cocotb.logging.DEBUG)

    def load_file(self, path: str, params: dict) -> (dict, list, list, dict):
        """function for loading data from configuration files.

            Args:
                path: path to the file.
                params: parametres of the component used for the hash function (mvb_key_width, hash_key_width, hash_width)

            Returns:
                comp_conf: the whole configuration of the component
                out_config: configuration that is uploaded into the component is configuration through file is used.
                out_keys: list of MVB keys that have data tied to them.
                out_data: dictionary of data to be uploaded into the component indexed by their respective keys.
        """

        out_config = list()
        out_keys = list()
        out_data = dict()
        tables = ["TOEPLITZ", "SIMPLE_XOR"]
        hash_functions = {"TOEPLITZ": toeplitz_hash, "SIMPLE_XOR": simple_xor_hash}

        fp = open(path, 'r')

        yaml_data = yaml.safe_load(fp)
        comp_conf = yaml_data["mvb_hash_table_simple"]

        params["hash_key"] = comp_conf["hash_key"]

        for i in range(comp_conf["num_of_tables"]):
            table = list()

            table_raw_data = comp_conf[tables[i]]

            for j in range(len(table_raw_data)):
                record = table_raw_data[j]["record"]

                mvb_key = record["mvb_key"]
                data = record["data"]

                h = hash_functions[tables[i]](mvb_key, params)

                out_keys.append(mvb_key)
                out_data[mvb_key] = data

                table.append([h, (mvb_key << (self.stream_out._item_width * 8 + 1)) + ((data << 1) + 1)])

            out_config.append(table)

        fp.close()

        return comp_conf, out_config, out_keys, out_data

    def model(self, transaction):
        """Model the DUT based on the input transaction"""
        self.expected_output.append(transaction)
        self.pkts_sent += 1

    async def reset(self) -> None:
        self.dut.RST.value = 1
        await ClockCycles(self.dut.CLK, 2)
        self.dut.RST.value = 0
        await RisingEdge(self.dut.CLK)


@cocotb.test()
async def run_test(dut, config_file: str = "test_configs/test_config_1B.yaml", config_method: str = "script", pkt_count: int = 10000):
    # Function that runs the cocotb test

    # Args:
    #     dut: dut
    #     config_file: file from which is to be loaded the configuration to be uploaded into the component.
    #     config_method: how is the component to be configured. There are two options: directly from the file ('file'),
    #                    or via configuration script to which is the file passed ('script').
    #     pkt_count: how many random packets are to be generated.

    cocotb.start_soon(Clock(dut.CLK, 5, units='ns').start())
    tb = testbench(dut, debug=True)
    await tb.reset()

    tb.backpressure.start((1, i % 5) for i in itertools.count())

    """Reading configuration from the component."""
    mvb_items = int.from_bytes(await tb.mi_interface.read32(_MVB_ITEMS), 'little')
    mvb_key_width = int.from_bytes(await tb.mi_interface.read32(_MVB_KEY_WIDTH), 'little')
    data_out_width = int.from_bytes(await tb.mi_interface.read32(_DATA_OUT_WIDTH), 'little')
    hash_width = int.from_bytes(await tb.mi_interface.read32(_HASH_WIDTH), 'little')
    hash_key_width = int.from_bytes(await tb.mi_interface.read32(_HASH_KEY_WIDTH), 'little')
    table_capacity = int.from_bytes(await tb.mi_interface.read32(_TABLE_CAPACITY), 'little')

    mvb_key_width_bytes = mvb_key_width // 8
    data_out_width_bytes = data_out_width // 8

    hash_func_params = {"mvb_key_width": mvb_key_width, "hash_key_width": hash_key_width, "hash_width": hash_width}

    cocotb.log.debug(f"MVB_ITEMS: {mvb_items}")
    cocotb.log.debug(f"MVB_KEY_WIDTH: {mvb_key_width}")
    cocotb.log.debug(f"DATA_OUT_WIDTH: {data_out_width}")
    cocotb.log.debug(f"HASH_WIDTH: {hash_width}")
    cocotb.log.debug(f"HASH_KEY_WIDTH: {hash_key_width}")
    cocotb.log.debug(f"TABLE_CAPACITY: {table_capacity}")

    """Asserting that the read configuration match configuration of the drivers connected to the component."""
    assert mvb_items == tb.stream_in._items
    assert mvb_key_width_bytes == tb.stream_in._item_width
    assert data_out_width_bytes == tb.stream_out._item_width
    assert hash_width == log2(table_capacity)

    """Loading configuration from a config file"""
    comp_conf, config, model_keys, model_data = tb.load_file(config_file, hash_func_params)

    """Asserting that parametres of component match with parametres in config file"""
    assert mvb_key_width == comp_conf["mvb_key_width"]
    assert data_out_width == comp_conf["data_out_width"]
    assert hash_width == comp_conf["hash_width"]
    assert hash_key_width == comp_conf["hash_key_width"]
    assert table_capacity == comp_conf["table_capacity"]

    item_width = mvb_key_width_bytes

    """Component can be configured from directly from a config file or via script in sw.toolkit configured by the same file."""
    if config_method == "file":
        hash_key_bytes = comp_conf["hash_key"].to_bytes(comp_conf["hash_key_width"] // 8, 'little')

        for i in range(ceildiv(4, len(hash_key_bytes))):
            await tb.mi_interface.write32(_HASH_KEY_REG, hash_key_bytes[4*i:4*(i+1)])

        await tb.mi_interface.write32(_COMMAND_REG, _CLEAR_TABLES.to_bytes(1, 'little'))

        for i in range(len(config)):
            await tb.mi_interface.write32(_COMMAND_REG, (i).to_bytes(1, "little"))

            for j in range(len(config[i])):
                address_bytes = config[i][j][0].to_bytes(mvb_key_width_bytes, 'little')
                data_bytes = config[i][j][1].to_bytes(mvb_key_width_bytes + data_out_width_bytes + 1, 'little')

                await tb.mi_interface.write32(_ADDR_REG, address_bytes)

                for k in range(ceildiv(4, len(data_bytes))):
                    await tb.mi_interface.write32(_DATA_REG, data_bytes[4*k:4*(k+1)])

                await tb.mi_interface.write32(_COMMIT_REG, b'\x00')

    elif config_method == "script":
        dtb = get_dtb(
            comp_name="MVB_HASH_TABLE_SIMPLE",
            comp_base=0,
            comp_offset=0x40,
            compatible_str="cesnet,ndk,mvb_hash_table_simple",
            bus_name="MI",
            version=17)

        servicer = Servicer(device=tb.mi_interface, dtb=dtb)
        dev = await cocotb.external(nfb.open)(servicer.path())

        await cocotb.external(MVB_HASH_TABLE_SIMPLE_TOOLKIT)(mod_path=config_file, dev=dev)

    else:
        raise RuntimeError("Invalid configuration setting.")

    await ClockCycles(dut.CLK, 10)

    for transaction in random_packets(item_width, item_width, pkt_count):
        int_transaction = int.from_bytes(transaction, "little")

        if int_transaction in model_keys:
            tb.model((model_data[int_transaction].to_bytes(data_out_width_bytes, 'little'), 1))
        else:
            tb.model(((0).to_bytes(data_out_width_bytes, 'little'), 0))

        cocotb.log.info(f"generated transaction: {transaction.hex()}")
        tb.stream_in.append(transaction)

    last_num = 0

    while (tb.stream_out.item_cnt < pkt_count):
        if (tb.stream_out.item_cnt // 1000) > last_num:
            last_num = tb.stream_out.item_cnt // 1000
            cocotb.log.info(f"Number of random transactions processed: {tb.stream_out.item_cnt}/{pkt_count}")
        await ClockCycles(dut.CLK, 100)

    raise tb.scoreboard.result
