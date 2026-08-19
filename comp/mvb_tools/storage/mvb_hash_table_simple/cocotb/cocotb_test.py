# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <ondrejschwarz@cesnet.cz>

"""
This test requires a configuration file to function.
You could either choose one of the prepared ones in the
'test_configs' directory or create your own via configuration
script in the 'sw' directory and running it with -i (interactive)
argument.
"""


import cocotb
import logging
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb.types import LogicArray
from cocotbext.ofm.mi.drivers import MIRequestDriver as MIDriver
from cocotbext.ofm.mvb.drivers import MVBDriver
from cocotbext.ofm.mvb.monitors import MVBMonitor
from cocotbext.ofm.mvb.protocol import MvbProtocol
from cocotbext.ofm.base.protocol import optional_signal
from cocotbext.ofm.base.types import LogicArray2D
from cocotbext.ofm.ver.backpressure import BackpressureGenerator, BackpressureConfig
from cocotbext.ofm.ver.generators import random_packets
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard

import nfb
from ofm.comp.mvb_tools.storage.mvb_hash_table_simple.mvb_hash_table_simple import MvbHashTableSimple, toeplitz_hash, simple_xor_hash
from cocotbext.ofm.utils.servicer import Servicer
from cocotbext.ofm.utils.device import create_dtb_simple
from cocotbext.ofm.utils.math import ceildiv
from transaction import MvbReqTrHashTableSimple, MvbResTrHashTableSimple

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


class MvbHashTableSimpleProtocol(MvbProtocol):
    @optional_signal
    def key(self, sigval: LogicArray) -> LogicArray2D:
        return LogicArray2D.from_logicarray(sigval, self.items)

    @key.write()
    def key(self, signal, value: LogicArray | LogicArray2D) -> None:
        if isinstance(value, LogicArray2D):
            value = value.serialize()
        signal.value = value


class testbench():
    def __init__(self, dut, debug=False) -> None:
        self.dut = dut
        self.stream_in = MVBDriver(dut, "RX_MVB", dut.CLK, protocol=MvbHashTableSimpleProtocol, generics_prefix="MVB")
        self.backpressure = BitDriver(dut.TX_MVB_DST_RDY, dut.CLK)
        self.stream_out = MVBMonitor(dut, "TX_MVB", dut.CLK, tr_type=MvbResTrHashTableSimple)
        self.mi_interface = MIDriver(dut, "MI", dut.CLK)

        self.stream_out.bus.dst_rdy.value = 1

        # Create a scoreboard on the stream_out bus
        self.pkts_sent = 0
        self.expected_output = []
        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.stream_out, self.expected_output)

        if debug:
            self.stream_in.log.setLevel(logging.DEBUG)
            self.stream_out.log.setLevel(logging.DEBUG)
            self.mi_interface.log.setLevel(logging.DEBUG)

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

                table.append([h, (mvb_key << ((self.stream_out.item_widths["data"] // 8) * 8 + 1)) + ((data << 1) + 1)])

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

    cocotb.start_soon(Clock(dut.CLK, 5, unit='ns').start())
    tb = testbench(dut, debug=False)
    await tb.reset()

    tb.backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    """Reading configuration from the component."""
    mvb_items = await tb.mi_interface.read32(_MVB_ITEMS)
    mvb_key_width = await tb.mi_interface.read32(_MVB_KEY_WIDTH)
    data_out_width = await tb.mi_interface.read32(_DATA_OUT_WIDTH)
    hash_width = await tb.mi_interface.read32(_HASH_WIDTH)
    hash_key_width = await tb.mi_interface.read32(_HASH_KEY_WIDTH)
    table_capacity = await tb.mi_interface.read32(_TABLE_CAPACITY)

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
    assert mvb_items == dut.MVB_ITEMS.value
    assert mvb_key_width_bytes == dut.MVB_KEY_WIDTH.value // 8 # FIXME
    assert data_out_width_bytes == tb.stream_out.item_widths["data"] // 8 # FIXME
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
            await tb.mi_interface.write(_HASH_KEY_REG, hash_key_bytes[4*i:4*(i+1)])

        await tb.mi_interface.write(_COMMAND_REG, _CLEAR_TABLES.to_bytes(1, 'little'))

        for i in range(len(config)):
            await tb.mi_interface.write(_COMMAND_REG, (i).to_bytes(1, "little"))

            for j in range(len(config[i])):
                address_bytes = config[i][j][0].to_bytes(mvb_key_width_bytes, 'little')
                data_bytes = config[i][j][1].to_bytes(mvb_key_width_bytes + data_out_width_bytes + 1, 'little')

                await tb.mi_interface.write(_ADDR_REG, address_bytes)

                for k in range(ceildiv(4, len(data_bytes))):
                    await tb.mi_interface.write(_DATA_REG, data_bytes[4*k:4*(k+1)])

                await tb.mi_interface.write(_COMMIT_REG, b'\x00')

    elif config_method == "script":
        dtb = create_dtb_simple(
            comp_name="MVB_HASH_TABLE_SIMPLE",
            comp_base=0,
            comp_size=0x40,
            compatible_str="cesnet,ndk,mvb_hash_table_simple")

        servicer = Servicer(device=tb.mi_interface, dtb=dtb)
        dev = await cocotb.task.bridge(nfb.open)(servicer.path())

        await cocotb.task.bridge(MvbHashTableSimple)(mod_path=config_file, dev=dev)

    else:
        raise RuntimeError("Invalid configuration setting.")

    await ClockCycles(dut.CLK, 10)

    for transaction in random_packets(item_width, item_width, pkt_count):
        int_transaction = int.from_bytes(transaction, "little")

        # creating response transactions to be compared with transactions generated by the monitor
        mvb_res_tr = MvbResTrHashTableSimple()
        if int_transaction in model_keys:
            mvb_res_tr.data = model_data[int_transaction]
            mvb_res_tr.match = 1
        else:
            mvb_res_tr.data = 0
            mvb_res_tr.match = 0
        tb.model(mvb_res_tr)

        # creating request transaction to be send by the driver
        mvb_req_tr = MvbReqTrHashTableSimple()
        mvb_req_tr.key = int_transaction

        cocotb.log.debug(f"generated transaction: {hex(mvb_req_tr.key)}")
        tb.stream_in.append(mvb_req_tr)

    last_num = 0

    while (tb.stream_out.item_cnt < pkt_count):
        if (num := tb.stream_out.item_cnt // 1000) > last_num:
            last_num = num
            cocotb.log.info(f"Number of random transactions processed: {tb.stream_out.item_cnt}/{pkt_count}")
        await ClockCycles(dut.CLK, 100)

    raise tb.scoreboard.result
