#!/usr/bin/env python

# main.py: Simple MVB Search Engine Toolkit
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""
This is a script for creating, editing and applying configuration files for MVB_HASH_TABLE_SIMPLE component (later just component).

Usage:
    The script can be used standalone or with the cocotb test for the component.
    If you already have a configuration file, you can use the script in 'silent mode', that is run it directly through the command line
    with the config file passed to use it to configure the component.
    If you don't have a config file yet and wish to create it, or you want to configure the component manually, use 'interactive mode.'

Arguments:
    -d 'path/to/device': path to the device to be configured. (mandatory)
    -c 'path/to/config/file': config file to be loaded or used to configure the component (mandatory -i is not passed, otherwise voluntary)
    -i: enter interactive mode (mandatory if -c is not passed, otherwise voluntary)

"""

import nfb
from cocotb.types import LogicArray, Range
from cocotbext.ofm.utils.math import ceildiv
import colorama
import sys
from math import log2
import yaml


class MVB_HASH_TABLE_SIMPLE_TOOLKIT(nfb.BaseComp):
    """Class used for creating, editing and applying configuration files for MVB_HASH_TABLE_SIMPLE component.

    Atributes:
        conected_to_comp(bool): if connection to component by loading a device tree was sucessfully established
        hash_key, mvb_key_width, data_out_width, table_capacity, hash_width, hash_key_width, num_of_tables: configuration parametres of connected MVB_HASH_TABLE_SIMPLE. If none is connected, default values for MVB_HASH_TABLE_SIMPLE.
        hash_func_params: dictionary of component parametres for hash functions
        t_hash_table, x_hash_table: lists of all data to be saved to hash tables.
        t_keys, x_keys: lists of MVB keys that have data adjacent to them in the respective hash tables.
        t_used, x_used: number of occupied positions in the respective hash tables.
        t_params, x_params: list including all the params above plus the name of the table.
        commands: dictionary of all commands that can be used in interactive mode.

    """

    # DevTree compatible string
    DT_COMPATIBLE = "cesnet,ndk,mvb_hash_table_simple"

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

    def __init__(self, inter=False, mod_path="", **kwargs) -> None:
        self._name = "MVB_HASH_TABLE_SIMPLE"

        self.hash_key = 2534237992  # 10884469298454947624

        """Setting defaults to component configuration parametres."""
        self.conected_to_comp = False
        self.mvb_key_width = 8
        self.data_out_width = 8
        self.table_capacity = 256
        self.hash_width = int(log2(self.table_capacity))
        self.hash_key_width = 32
        self.num_of_tables = 2

        self.hash_func_params = {
            "hash_key": self.hash_key,
            "mvb_key_width": self.mvb_key_width,
            "hash_key_width": self.hash_key_width,
            "hash_width": self.hash_width
        }

        """Setting script parametres."""
        self.t_keys = list()
        self.t_hash_table = self.table_capacity * [[False, 0]]
        self.t_used = 0
        self.t_params = ["TOEPLITZ", toeplitz_hash, self.t_keys, self.t_hash_table, self.t_used]

        self.x_keys = list()
        self.x_hash_table = self.table_capacity * [[False, 0]]
        self.x_used = 0
        self.x_params = ["SIMPLE_XOR", simple_xor_hash, self.x_keys, self.x_hash_table, self.x_used]

        self.commands = {
            "add": self.comm_add,
            "replace": self.comm_replace,
            "remove": self.comm_remove,
            "clear": self.comm_clear,
            "list": self.comm_list,
            "commit": self.comm_commit,
            "save": self.comm_save,
            "load": self.comm_load,
            "hash": self.comm_hash,
            "testkey": self.comm_testkey,
            "comparehashes": self.comm_comparehashes,
            "hwconfig": self.comm_hwconfig,
            "help": self.comm_help
        }

        """Setting up servicer."""
        try:
            super().__init__(**kwargs)
            if "index" in kwargs:
                self._name += " " + str(kwargs.get("index"))

            self.get_hw_config()

            self.conected_to_comp = True

        except Exception:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Failed to open {self._name} component.")

        if mod_path != "":
            self.comm_load(mod_path, silent=True)

        if inter:
            self.command_line()
        else:
            self.comm_commit(silent=True)

    def get_params(self, table: str) -> list:
        """Gets parametres of the requested table.
            Args:
                table: name of the table

            Returns:
                parametres of the chosen table

        """

        params = self.t_params if table == "toeplitz" else None
        params = self.x_params if table == "xor" else params

        return params

    def adapt_type(self, data):
        try:
            if float(data) == int(data):
                return int(data)
            else:
                return float(data)
        except Exception:
            return str(data)

    def get_hw_config(self) -> None:
        """Reads configuration of the connected MVB_HASH_TABLE_SIMPLE component"""

        self.mvb_key_width = self._comp.read32(self._MVB_KEY_WIDTH)
        self.data_out_width = self._comp.read32(self._DATA_OUT_WIDTH)
        self.hash_width = self._comp.read32(self._HASH_WIDTH)
        self.hash_key_width = self._comp.read32(self._HASH_KEY_WIDTH)
        self.table_capacity = self._comp.read32(self._TABLE_CAPACITY)

        self.hash_func_params = {
            "hash_key": self.hash_key,
            "mvb_key_width": self.mvb_key_width,
            "hash_key_width": self.hash_key_width,
            "hash_width": self.hash_width
        }

        self.hash_func_params = {
            "hash_key": self.hash_key,
            "mvb_key_width": self.mvb_key_width,
            "hash_key_width": self.hash_key_width,
            "hash_width": self.hash_width
        }

    def test_key(self, hash_function) -> int:
        """Tests the requested hash function for internal collisions caused by the key, where collision is a situation,
        where same hash is calcuted for one or more different keys from the whole range of the key's values. If lot of
        collisions occur, it's best to consider using a different hash key.

        Args:
            hash_funtion: reference to a function used for calculating the hash (in other words, the hash function function :D).

        Returns:
            Number or found collisions.

        """

        hashes = list()
        collisions = 0

        for i in range(self.table_capacity):
            h = hash_function(i, self.hash_func_params)

            if h in hashes:
                collisions += 1
            else:
                hashes.append(h)

        return collisions

    def test_collisions(self, hash_function1, hash_function2) -> list:
        """Tests collisions between two different hash functions, where collision is a situation, where for the same key both
        hash functions calculate the same hash.

        Args:
            hash_function1: reference to a function used for calculating the hash (in other words, the hash function function :D).
            hash_function2: a hash function function different from hash_function1.
        Returns:
            List of keys for which collisions accured.

        """

        collisions = list()

        for i in range(self.table_capacity):
            if hash_function1(i, self.hash_func_params) == hash_function2(i, self.hash_func_params):
                collisions.append(f"{i} -> {hash_function1(i, self.hash_func_params)}")

        return collisions

    def command_line(self) -> None:
        """Main interface of the interactive mode used to input commands. Runs until the 'exit' or 'quit' commands.
        All the command line commands are prefixed with 'comm'."""

        print(f"{colorama.Fore.BLUE + colorama.Style.BRIGHT}MVB HASH TABLE SIMPLE TOOLKIT, version 0.1\nCopyright (C) 2024 CESNET z. s. p. o.\nInput command 'help' for more info.\n{colorama.Style.RESET_ALL}")

        while True:
            arguments = input(f"{colorama.Fore.BLUE + colorama.Style.BRIGHT}>>> {colorama.Style.RESET_ALL}").split(" ")

            for i in range(len(arguments)):
                arguments[i] = self.adapt_type(arguments[i])

            command, arguments = arguments[0], arguments[1:]

            if command == "exit" or command == "quit":
                return
            else:
                try:
                    self.commands.get(command, self.error)(*arguments)
                except Exception:
                    self.error()

    def comm_add(self, key: int = None, data: int = None, table: str = "toeplitz", recurse=False) -> None:
        """Adds a value to a chosen table, the position of the value is decided by the hash of the key.

        Args:
            key: mvb key, to which is the added value to be connected. The hash that decided position of the value in table
            is calculated from this number.
            data: value to be added to the table.
            table: decided to which table is the value to be added to. Toeplitz table is chosen by default, other option is
            'xor' for adding to the simple xor table.

        """
        if key is None or data is None:
            print(f"{colorama.Fore.RED}{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL}{colorama.Style.RESET_ALL} Invalid arguments. Usage of add: add (key) (data) (table=[*toeplitz, xor]).")
            return

        try:
            key.to_bytes(self.mvb_key_width // 8, 'little')
        except Exception:
            print(f"{colorama.Fore.RED}{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL}{colorama.Style.RESET_ALL} Key value {key} can't be represented on {self.mvb_key_width} bits.")
            return

        try:
            data.to_bytes(self.data_out_width // 8, 'little')
        except Exception:
            print(f"{colorama.Fore.RED}{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL}{colorama.Style.RESET_ALL} Data value {data} can't be represented on {self.data_out_width} bits.")
            return

        if key in self.t_keys or key in self.x_keys:
            print(f"{colorama.Fore.RED}{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL}{colorama.Style.RESET_ALL} Key already in use.")
            return

        params = self.get_params(table)

        if params is None:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid table. Possible tables are both, toeplitz, xor.")
            return

        name = params[0]
        hash_function = params[1]
        keys = params[2]
        hash_table = params[3]
        used = params[4]

        if used < self.table_capacity:
            hash_key = hash_function(key, self.hash_func_params)

            if hash_table[hash_key][0] is False:
                keys.append(key)
                hash_table[hash_key] = [True, data]

                used += 1
                self.t_params[4] += 1 if table == "toeplitz" else 0
                self.x_params[4] += 1 if table == "xor" else 0

                print(f"{colorama.Fore.GREEN}Success:{colorama.Style.RESET_ALL} Record number {used - 1} sucessfully added to position {hash_key} in {name} TABLE.")

            else:
                if self.num_of_tables == 1 or recurse:
                    print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Record can't be added, position {hash_key} in {name} TABLE is already occupied. You can save it to a different one or use replace (table=[toeplitz, xor]) (record_num) (key) (data) to replace it or remove (mode=[record, hash]) (table=[toeplitz, xor]) (num) to delete it.")
                    return
                else:
                    sec_table = "xor" if table == "toeplitz" else "toeplitz"
                    print(f"{colorama.Fore.RED}Warning:{colorama.Style.RESET_ALL} Record can't be added, position {hash_key} in {name} TABLE is already occupied. Trying to save into the {self.get_params(sec_table)[0]} table.")
                    self.comm_add(key, data, sec_table, recurse=True)
        else:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Record can't be added, because {name} TABLE is full. You can save it to a different one or use replace (table=[toeplitz, xor]) (record_num) (key) (data)  or remove (mode=[record, hash]) (table=[toeplitz, xor]) (num) to make space.")

    def comm_list(self, mode: str = None, table: str = "both") -> None:
        """Lists the contents of the table(s).

            Args:
                mode: 'record' lists only valid records, 'table' lists the whole table(s).
                table: which table should be listed or if both should be listed. Both are chosen by default.

        """

        if mode is None:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid arguments. Usage of list: list (mode=[records, table]) (table=[*both, toeplitz, xor]).")
            return

        params = [self.t_params, self.x_params] if table == "both" else None
        params = [self.t_params] if table == "toeplitz" else params
        params = [self.x_params] if table == "xor" else params

        if params is None:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid table. Possible tables are both, toeplitz, xor.")
            return

        for i in range(len(params)):
            name = params[i][0]
            hash_function = params[i][1]
            keys = params[i][2]
            hash_table = params[i][3]
            used = params[i][4]

            if mode == "records":
                print(f"\n{colorama.Fore.GREEN  + colorama.Style.BRIGHT}{name} TABLE:{colorama.Style.RESET_ALL}")

                if used == 0:
                    print("No records.\n")
                    continue

                for j in range(used):
                    hash_key = hash_function(keys[j], self.hash_func_params)
                    print(f"\n{colorama.Fore.BLUE  + colorama.Style.BRIGHT}RECORD {j}:{colorama.Style.RESET_ALL}\n\tPOSITION = {hash_key}\n\tKEY = {keys[j]}\n\tDATA = {hash_table[hash_key][1]}")

                print(f"\n {colorama.Fore.BLUE  + colorama.Style.BRIGHT}{used} used, {self.table_capacity - used} free.{colorama.Style.RESET_ALL}\n")

            elif mode == "table":
                print(f"\n{colorama.Fore.GREEN  + colorama.Style.BRIGHT}{name} TABLE:{colorama.Style.RESET_ALL}\n")

                for j in range(self.table_capacity):
                    if hash_table[j][0]:
                        color = colorama.Fore.GREEN
                    else:
                        color = colorama.Fore.RED

                    print(f"{color}{j}: VALID = {hash_table[j][0]} ; DATA = {hash_table[j][1]}")

                print(f"\n {colorama.Fore.BLUE + colorama.Style.BRIGHT}{used} used, {self.table_capacity - used} free.{colorama.Style.RESET_ALL}\n")

            else:
                print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid arguments. Usage of list: list (mode=[records, table]) (table=[*both, toeplitz, xor]).")
                return

    def comm_replace(self, table: str = None, record_num: int = None, key: str = None, data: str = None) -> None:
        """Replaces record with a diffent one.

        Args:
            table: in which table are the data to be replaced located, 'toeplitz' or 'xor'.
            record_num: number tied to the record to be replaced.
            key: the new key.
            data: the new data.

        """

        if table is None or record_num is None or key is None or data is None:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid arguments. Usage of replace: replace (table=[toeplitz, xor]) (num) (key) (data).")
            return

        params = self.get_params(table)

        if params is None:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid table. Possible tables are both, toeplitz, xor.")
            return

        name = params[0]
        hash_function = params[1]
        keys = params[2]
        hash_table = params[3]
        used = params[4]

        if record_num < used:
            hash_key = hash_function(key, self.hash_func_params)

            self.comm_remove("record", table, record_num, silent=True)

            keys.insert(record_num, key)
            hash_table[hash_key] = [True, data]

            self.t_params[4] += 1 if table == "toeplitz" else 0
            self.x_params[4] += 1 if table == "xor" else 0

            print(f"{colorama.Fore.GREEN}Success:{colorama.Style.RESET_ALL} Record number {record_num} sucessfully ovewritten and added to position {hash_key} in {name} TABLE.")

        else:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Record {record_num} is out of range of 0:{self.t_used - 1} indexes of records.")

    def comm_remove(self, mode: str = None, table: str = None, num: int = None, silent: bool = False) -> None:
        """Removes record from the chosen table, or data directly from the table and the tied record.

        Args:
            mode: if the passed number indicates record ('record') or a position in the table ('hash').
            table: for which table is the operation intended, 'toeplitz' or 'xor'.
            num: number of the record or the position in the table (hash).
            silent: if True, cancels print-outs.

        """

        if table is None or mode is None or num is None:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid arguments. Usage of remove: remove (mode=[record, hash]) (table=[toeplitz, xor]) (num).")
            return

        params = self.get_params(table)

        if params is None:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid table. Possible tables are both, toeplitz, xor.")
            return

        hash_function, keys, hash_table, used = params[1:5]

        if mode == "record":
            if num < used:
                hash_key = hash_function(keys[num], self.hash_func_params)
                hash_table[hash_key][0] = False
                del keys[num]

                self.t_params[4] -= 1 if table == "toeplitz" else 0
                self.x_params[4] -= 1 if table == "xor" else 0

                if not silent:
                    print(f"{colorama.Fore.GREEN}Success:{colorama.Style.RESET_ALL} Record {num} successfully removed.")

            else:
                print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Record {num} is out of range of 0:{used - 1} indexes of records.")

        elif mode == "hash":
            if num < self.table_capacity:
                if hash_table[num][0] is True:
                    hash_table[num][0] = False

                    for i in range(used):
                        # print(f"DEBUG: self.t_keys: {self.t_keys}")
                        # print(f"DEBUG: i: {i}, self.t_keys[{i}] = {self.t_keys[i]}")
                        if num == hash_function(keys[i], self.hash_func_params):
                            del keys[i]
                            break

                    self.t_params[4] -= 1 if table == "toeplitz" else 0
                    self.x_params[4] -= 1 if table == "xor" else 0

                    print(f"{colorama.Fore.GREEN}Success:{colorama.Style.RESET_ALL} Record on position {num} successfully removed.")

                else:
                    print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Position {num} is already empty.")

            else:
                print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Position {num} is out of range of 0:{self.table_capacity - 1} indexed of hash_table.")

        else:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid mode. The possible modes are: record, hash")

    def comm_clear(self, table: str = None, silent=False) -> None:
        """Clears all data in the chosen table.

        Args:
            table: which table shall be cleared.
            silent: cancels print outs.

        """
        if table is None:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid arguments. Usage of clear: clear (table=[toeplitz, xor]).")
            return

        params = self.get_params(table)

        if params is None:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid table. Possible tables are both, toeplitz, xor.")
            return

        clear_safe_switch = False

        if not silent:
            clear_safe_switch = input(f"{colorama.Fore.RED}You are about to delete all records in {params[0]} TABLE. Are you sure? (y/n) {colorama.Style.RESET_ALL}") == "y"

        if clear_safe_switch or silent:
            params[2].clear()
            params[3] = self.table_capacity * [[False, 0]]

            self.t_params[4] = 0 if table == "toeplitz" else self.t_params[4]
            self.x_params[4] = 0 if table == "xor" else self.x_params[4]

            if not silent:
                print(f"{colorama.Fore.GREEN}Success:{colorama.Style.RESET_ALL} {params[0]} TABLE has been cleared.")
        else:
            if not silent:
                print("Clear operation aborted.")

    def comm_hwconfig(self) -> None:
        """Prints out the configuration of the connected component. If no component is connected, prints out defaults."""

        print(f"\n{colorama.Fore.BLUE + colorama.Style.BRIGHT}CONNECTED TO COMPONENT:{colorama.Style.RESET_ALL} {self.conected_to_comp}")
        print(f"\n{colorama.Fore.BLUE + colorama.Style.BRIGHT}MVB_KEY_WIDTH:{colorama.Style.RESET_ALL} {self.mvb_key_width}\n{colorama.Fore.BLUE + colorama.Style.BRIGHT}DATA_OUT_WIDTH:{colorama.Style.RESET_ALL} {self.data_out_width}\n{colorama.Fore.BLUE + colorama.Style.BRIGHT}HASH_WIDTH:{colorama.Style.RESET_ALL} {self.hash_width}\n{colorama.Fore.BLUE + colorama.Style.BRIGHT}self.hash_key_WIDTH:{colorama.Style.RESET_ALL} {self.hash_key_width}\n{colorama.Fore.BLUE + colorama.Style.BRIGHT}TABLE_CAPACITY:{colorama.Style.RESET_ALL} {self.table_capacity}\n")

    def comm_commit(self, silent: bool = False) -> None:
        """Upload data from the tables to component.

        Args:
            silent: if True, cancels print-outs.

        """

        if not self.conected_to_comp:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Can't commit, connection to component not active.")
            return

        if not silent:
            if input("Commit to component? (y/n): ") == "n":
                print("Commit operation aborted.")
                return

        hash_key_bytes = (self.hash_key).to_bytes(self.hash_key_width // 8, 'little')

        for i in range(ceildiv(4, len(hash_key_bytes))):
            self._comp.write32(self._HASH_KEY_REG, int.from_bytes(hash_key_bytes[4 * i: 4 * (i + 1)], 'little'))

        self._comp.write32(self._COMMAND_REG, self._CLEAR_TABLES)

        params = [self.t_params, self.x_params]

        for i in range(self.num_of_tables):
            self._comp.write32(self._COMMAND_REG, i)

            # name = params[i][0]
            hash_function, keys, hash_table, used = params[i][1:5]

            for j in range(len(keys)):
                hash_key = hash_function(keys[j], self.hash_func_params)
                address_bytes = hash_key.to_bytes(self.mvb_key_width // 8, 'little')
                data_bytes = ((int(keys[j]) << (self.data_out_width + 1)) + (hash_table[hash_key][1] << 1) + 1).to_bytes((self.mvb_key_width // 8) + (self.data_out_width // 8) + 1, 'little')

                self._comp.write32(self._ADDR_REG, int.from_bytes(address_bytes, 'little'))

                for k in range(ceildiv(4, len(data_bytes))):
                    self._comp.write32(self._DATA_REG, int.from_bytes(data_bytes[4 * k: 4 * (k + 1)], 'little'))

                self._comp.write32(self._COMMIT_REG, 0)

    def comm_save(self, path: str = None, silent: bool = False) -> None:
        """Save configuration to a file.

        Args:
            path: path, where is the config file to be saved.
            silent: if True, cancels print-outs.

        """
        if path is None:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid arguments. Usage of save: save (path).")
            return
        try:
            fp = open(path, 'w+')
        except Exception:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Failed to create file {path}.")
            return

        yaml_data = dict()
        comp_conf = dict()

        yaml_data["mvb_hash_table_simple"] = comp_conf

        comp_conf["hash_key"] = self.hash_key
        comp_conf["mvb_key_width"] = self.mvb_key_width
        comp_conf["data_out_width"] = self.data_out_width
        comp_conf["table_capacity"] = self.table_capacity
        comp_conf["hash_width"] = self.hash_width
        comp_conf["hash_key_width"] = self.hash_key_width
        comp_conf["num_of_tables"] = self.num_of_tables

        params = [self.t_params, self.x_params]

        for i in range(self.num_of_tables):
            name = params[i][0]
            hash_function = params[i][1]
            keys = params[i][2]
            hash_table = params[i][3]
            used = params[i][4]

            yaml_hash_table = comp_conf[name] = list()

            for j in range(used):
                record_wrap = dict()
                record = dict()
                h = hash_function(keys[j], self.hash_func_params)

                record_wrap["record"] = record

                record["mvb_key"] = keys[j]
                record["data"] = hash_table[h][1]

                yaml_hash_table.append(record_wrap)

        yaml.safe_dump(yaml_data, fp)
        fp.close()

        if not silent:
            print(f"{colorama.Fore.GREEN}Success:{colorama.Style.RESET_ALL} Configuration successfully saved to {path}.")

    def comm_load(self, path: str = None, silent: bool = False) -> None:
        """Loads config file.

        Args:
            path: path to the config file to be loaded
            silent: if True, cancels print-outs.
        """

        if path is None:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid arguments. Usage of load: load (path).")
            return

        if (len(self.t_keys) > 0 or len(self.x_keys) > 0) and not silent:
            if input(f"{colorama.Fore.RED}Warning:{colorama.Style.RESET_ALL} Unsaved changes will be ovewritten. Continue? (y/n) ") != "y":
                print("Load operation aborted.")
                return
        try:
            fp = open(path, 'r')
        except Exception:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Failed to open file {path}.")
            return

        params = [self.t_params, self.x_params]

        try:
            yaml_data = yaml.safe_load(fp)
        except Exception:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Failed to read yaml data.")
            return

        comp_conf = yaml_data.get("mvb_hash_table_simple", None)

        if comp_conf is None:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Configuration file not intended for MVB_HASH_TABLE_SIMPLE or in a wrong format.")
            return

        self.hash_key = comp_conf["hash_key"]

        if self.conected_to_comp:
            try:
                assert (self.mvb_key_width == comp_conf["mvb_key_width"])
                assert (self.data_out_width == comp_conf["data_out_width"])
                assert (self.table_capacity == comp_conf["table_capacity"])
                assert (self.hash_width == comp_conf["hash_width"])
                assert (self.hash_key_width == comp_conf["hash_key_width"])
                assert (self.num_of_tables == comp_conf["num_of_tables"])

            except Exception:
                print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Parameter missing or parametres in configuration file and in connected component don't match.")
                return

        else:
            self.mvb_key_width = comp_conf["mvb_key_width"]
            self.data_out_width = comp_conf["data_out_width"]
            self.table_capacity = comp_conf["table_capacity"]
            self.hash_width = comp_conf["hash_width"]
            self.hash_key_width = comp_conf["hash_key_width"]
            self.num_of_tables = comp_conf["num_of_tables"]

        self.hash_func_params = {
            "hash_key": self.hash_key,
            "mvb_key_width": self.mvb_key_width,
            "hash_key_width": self.hash_key_width,
            "hash_width": self.hash_width
        }

        for i in range(self.num_of_tables):
            clear_table = "toeplitz" if i == 0 else "xor"
            self.comm_clear(clear_table, silent=True)

            name = params[i][0]
            hash_function = params[i][1]
            keys = params[i][2]
            hash_table = params[i][3]

            table_data = comp_conf.get(name, [])

            for j in range(len(table_data)):
                try:
                    record = table_data[j]["record"]

                    mvb_key = record["mvb_key"]
                    h = hash_function(mvb_key, self.hash_func_params)
                    data = record["data"]

                    keys.append(mvb_key)
                    hash_table[h] = [True, data]
                    params[i][4] += 1

                except Exception:
                    print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Data in record missing or in wrong format.")
                    return

        fp.close()

        if not silent:
            print(f"{colorama.Fore.GREEN}Success:{colorama.Style.RESET_ALL} Configuration successfully loaded.")

    def comm_hash(self, hash_function: str = None, num: int = None) -> None:
        """Calculates hash from the passed number using the chosen hash function (used for testing).

        Args:
            hash_functions: 'toeplitz' or 'xor'
            num: number from which is the hash to be calculated.

        """

        if hash_function is None or num is None:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid arguments. Usage of hash: hash (hash_function=[toeplitz, xor]) (num).")
            return

        if hash_function == "toeplitz":
            print(toeplitz_hash(num, self.hash_func_params))
        elif hash_function == "xor":
            print(simple_xor_hash(num, self.hash_func_params))
        else:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Hash function '{hash_function}' not found.")

    def comm_testkey(self, hash_function=None) -> None:
        """Prints out the result of the test_key for the chosen hash function (used for testing).

        Args:
            hash_functions: 'toeplitz' or 'xor'

        """

        if hash_function is None:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid arguments. Usage of hash: testkey (hash_function=[toeplitz, xor]).")

        if hash_function == "toeplitz":
            print(f"Found {self.test_key(toeplitz_hash)} hash collisions.")
        elif hash_function == "xor":
            print(f"Found {self.test_key(simple_xor_hash)} hash collisions.")
        else:
            print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid hash function '{hash_function}'.")

    def comm_comparehashes(self) -> None:
        """Prints out results of the test_collisions function for toeplitz and simple xor functions (used for testing)."""

        collisions = self.test_collisions(toeplitz_hash, simple_xor_hash)

        for i in range(len(collisions)):
            print(f"{collisions[i]}\n")

        print(f"Number of collisions: {len(collisions)}")

    def comm_help(self) -> None:
        """Prints out help."""

        print(f"\nThis script is used for creating, editing and applying configuration files for MVB_HASH_TABLE_SIMPLE component.\n\n{colorama.Fore.BLUE + colorama.Style.BRIGHT}Commands:{colorama.Style.RESET_ALL}\n\tadd (key) (data) (table=[*toeplitz, xor]) {colorama.Fore.BLUE + colorama.Style.BRIGHT}- creates new record{colorama.Style.RESET_ALL}\n\tlist (mode=[records, table]) (table=[*both, toeplitz, xor]) {colorama.Fore.BLUE + colorama.Style.BRIGHT}- lists records or hash table{colorama.Style.RESET_ALL}\n\treplace (table=[toeplitz, xor]) (record_num) (key) (data) {colorama.Fore.BLUE + colorama.Style.BRIGHT}- replaces data in specified record with specified data{colorama.Style.RESET_ALL}\n\tremove (mode=[record, hash]) (table=[toeplitz, xor]) (num) {colorama.Fore.BLUE + colorama.Style.BRIGHT}- removes record by record number or hash number{colorama.Style.RESET_ALL}\n\tclear (table=[toeplitz, xor]) {colorama.Fore.BLUE + colorama.Style.BRIGHT}- deletes all records in specified table{colorama.Style.RESET_ALL}\n\tsave (path) {colorama.Fore.BLUE + colorama.Style.BRIGHT}- save configuration into a file{colorama.Style.RESET_ALL}\n\tload (path) {colorama.Fore.BLUE + colorama.Style.BRIGHT}- loads configuration from a file{colorama.Style.RESET_ALL}\n\thwconfig {colorama.Fore.BLUE + colorama.Style.BRIGHT}- displays configuration of the connected component{colorama.Style.RESET_ALL}\n\tcommit {colorama.Fore.BLUE + colorama.Style.BRIGHT}- uploads configuration to component{colorama.Style.RESET_ALL}\n\thash (hash_function=[toeplitz, xor]) (num) {colorama.Fore.BLUE + colorama.Style.BRIGHT}- calculates hash of specified number using specified hash function (debug){colorama.Style.RESET_ALL}\n\ttestkey (hash_function=[toeplitz, xor]) {colorama.Fore.BLUE + colorama.Style.BRIGHT}- tests hash key for collions (debug){colorama.Style.RESET_ALL}\n\tcomparehashes {colorama.Fore.BLUE + colorama.Style.BRIGHT}- test collions between toeplitz and simple xor hash functions (debug){colorama.Style.RESET_ALL}\n")

    def error(self) -> None:
        """Prints out generic error."""

        print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid command or arguments. Use command 'help' to view usage.")


def toeplitz_hash(mvb_key: int, params: dict) -> int:
    """Calculates hash using the toeplitz hash function.

    Args:
        mvb_key: integer for which the hash is to be calculated.
        params: dictionary containing parametres of the component (hash_key, mvb_key_width, hash_key_width, hash_width)

    Returns:
        Calculated hash.

    """

    hash_key = params["hash_key"]
    mvb_key_width = params["mvb_key_width"]
    hash_key_width = params["hash_key_width"]
    hash_width = params["hash_width"]

    hash_key_bits = LogicArray(hash_key, Range(hash_key_width-1, 'downto', 0))
    mvb_key_bits = LogicArray(mvb_key, Range(mvb_key_width-1, 'downto', 0))
    hash_bits = LogicArray(0, Range(hash_width-1, 'downto', 0))

    for i in Range(mvb_key_width-1, 'downto', 0):
        key_slice = hash_key_bits[hash_key_width-(mvb_key_width-1-i)-1 : hash_key_width-hash_width-(mvb_key_width-1-i)]
        key_hash = LogicArray(0, Range(hash_width-1, 'downto', 0))

        if mvb_key_bits[i]:
            key_hash = key_slice

        hash_bits = hash_bits ^ key_hash

    return hash_bits.integer


def simple_xor_hash(mvb_key: int, params: dict) -> int:
    """Calculates hash using the simple xor hash function.

    Args:
        mvb_key: integer for which the hash is to be calculated.
        params: dictionary containing parametres of the component (hash_key, mvb_key_width, hash_key_width, hash_width)

    Returns:
        Calculated hash.

    """

    hash_key = params["hash_key"]
    mvb_key_width = params["mvb_key_width"]
    hash_key_width = params["hash_key_width"]
    hash_width = params["hash_width"]

    hash_key_bits = LogicArray(hash_key, Range(hash_key_width, 'downto', 0))
    mvb_key_bits = LogicArray(mvb_key, Range(mvb_key_width, 'downto', 0))

    hash_bits = mvb_key_bits[hash_width-1 : 0] ^ hash_key_bits[hash_width-1 : 0]

    return hash_bits.integer


def main() -> None:
    """Main function of the script if run from the terminal."""

    comm = 0

    inter = False
    dev_path = ""
    mod_path = ""

    del sys.argv[0]

    if len(sys.argv) < 2:
        print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Not enough arguments. At least two are required, and those are: -d and -i or -d and -c")
        return

    for argv in sys.argv:
        if comm == 0:
            comm = 1 if argv == "-d" else comm
            comm = 2 if argv == "-c" else comm

            inter = True if argv == "-i" else inter

            if comm == 0 and argv != "-i":
                print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Invalid switch '{argv}'.")
                return

        else:
            dev_path = argv if comm == 1 else dev_path
            mod_path = argv if comm == 2 else mod_path

            comm = 0

    if dev_path == "":
        print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Mandatory argument dev_path not passed.")
        return

    dev = None

    try:
        dev = nfb.open(dev_path)
    except Exception:
        print(f"{colorama.Fore.RED}Error:{colorama.Style.RESET_ALL} Failed to open '{dev_path}' Starting in offline mode.")

    MVB_HASH_TABLE_SIMPLE_TOOLKIT(inter, mod_path, dev=dev)


if __name__ == "__main__":
    main()
