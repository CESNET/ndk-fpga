#!/bin/python3

# profile_generator.py: Generator for FlowTest ft-generator (https://github.com/CESNET/FlowTest/tree/main/tools/ft-generator) profile
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

# SPDX-License-Identifier: BSD-3-Clause

import csv
import json
import argparse
import time
import random
from typing import Optional
from typing import TextIO
from collections import KeysView
from requests.structures import CaseInsensitiveDict


class ProfileGenerator:

    ### PARAMETERS ##

    # Start/End time
    START_TIME_MIN = 0
    START_TIME_MAX = 1000
    END_TIME_MIN = 0
    END_TIME_MAX = 1000

    # Forward direction
    PACKETS_MIN_NUMBER = 10
    PACKETS_MAX_NUMBER = 100
    BYTES_PER_PACKET_MIN_NUMBER = 60
    BYTES_PER_PACKET_MAX_NUMBER = 1500

    BYTES_MIN_NUMBER = BYTES_PER_PACKET_MIN_NUMBER * PACKETS_MIN_NUMBER
    BYTES_MAX_NUMBER = BYTES_PER_PACKET_MAX_NUMBER * PACKETS_MAX_NUMBER

    # Opposite direction
    PACKETS_REV_MIN_NUMBER = 0
    PACKETS_REV_MAX_NUMBER = 100
    BYTES_PER_PACKET_REV_MIN_NUMBER = 60
    BYTES_PER_PACKET_REV_MAX_NUMBER = 1500

    BYTES_REV_MIN_NUMBER = BYTES_PER_PACKET_REV_MIN_NUMBER * PACKETS_REV_MIN_NUMBER
    BYTES_REV_MAX_NUMBER = BYTES_PER_PACKET_REV_MAX_NUMBER * PACKETS_REV_MAX_NUMBER

    # Record number
    RECORD_MIN_NUMBER = 10
    RECORD_MAX_NUMBER = 100

    ### INITIALIZING ###

    def __init__(self, config: Optional[CaseInsensitiveDict] = None) -> None:
        if config is not None:
            self.__apply_config(config)

    def __apply_config(self, config: CaseInsensitiveDict) -> None:
        parameters = [attribute for attribute in dir(self) if attribute[0].isupper()] # Gets only parameters (e.g. START_TIME_MIN)
        for parameter in parameters:
            if parameter in config:
                self.__dict__[parameter] = config[parameter]

    ### PROFILE GENERATION ###

    def __generate_record(self) -> dict:
        record = {}

        record['START_TIME'] = random.randint(self.START_TIME_MIN, self.START_TIME_MAX)
        record['END_TIME'] = random.randint(max(self.END_TIME_MIN, record['START_TIME']), self.END_TIME_MAX)

        record['L4_PROTO'] = random.choice([1, 6, 17, 58]) # ICMP, TCP, UDP and ICMPv6
        if record['L4_PROTO'] == 58: # L4 protocol ICMPv6 must be used with L3 protocol IPv6
            record['L3_PROTO'] = 6
        elif record['L4_PROTO'] == 1: # L4 protocol ICMP must be used with L3 protocol IPv4
            record['L3_PROTO'] = 4
        else:
            record['L3_PROTO'] = random.choice([4, 6]) # IPv4 and IPv6

        if (record['L4_PROTO'] != 6) and (record['L4_PROTO'] != 17): # Not TCP nor UDP
            record['SRC_PORT'] = 0
            record['DST_PORT'] = 0
        else:
            record['SRC_PORT'] = random.randint(0, 1023)
            record['DST_PORT'] = random.randint(0, 1023)

        record['PACKETS'] = random.randint(self.PACKETS_MIN_NUMBER, self.PACKETS_MAX_NUMBER)
        record['BYTES'] = random.randint(self.BYTES_MIN_NUMBER, self.BYTES_MAX_NUMBER)

        record['PACKETS_REV'] = random.randint(self.PACKETS_REV_MIN_NUMBER, self.PACKETS_REV_MAX_NUMBER)
        record['BYTES_REV'] = random.randint(self.BYTES_REV_MIN_NUMBER, self.BYTES_REV_MAX_NUMBER)
        if (record['PACKETS_REV'] == 0) or (record['BYTES_REV'] == 0): # In case any is 0
            record['PACKETS_REV'] = 0
            record['BYTES_REV'] = 0

        if record['PACKETS'] + record['PACKETS_REV'] == 1: # If flow has only 1 packet it must have start timestamp = end timestamp
            record['END_TIME'] = record['START_TIME']

        return record

    def __generate_records(self) -> list:
        records = []

        record_number = random.randint(self.RECORD_MIN_NUMBER, self.RECORD_MAX_NUMBER)
        for i in range(record_number):
            record = self.__generate_record()
            records.append(record)

        return records

    @staticmethod
    def __get_header_from_record(record: dict) -> KeysView:
        header = record.keys()
        return header

    def write_profile(self, profile_file: TextIO) -> None:
        records = self.__generate_records()
        header = self.__get_header_from_record(records[0])

        writer = csv.DictWriter(profile_file, fieldnames=header)
        writer.writeheader()
        writer.writerows(records)

### ARGUMENTS PARSING ###


def parse_arguments() -> argparse.Namespace:
    argument_parser = argparse.ArgumentParser()

    argument_parser.add_argument('-o', '--output', type=str, help='Output file for generated profile.', required=True)
    argument_parser.add_argument('-s', '--seed', type=int, help='Seed for randomization.', default=int(time.time() * 1000))
    argument_parser.add_argument('-c', '--config', type=str, help='Input configuration json file.', default=None)
    argument_parser.add_argument('--forward-packet-number', type=int, help='Number of packets in forward direction.', default=None)
    argument_parser.add_argument('--reverse-packet-number', type=int, help='Number of packets in reverse direction.', default=None)

    arguments = argument_parser.parse_args()
    return arguments

### MAIN ###


def main() -> None:
    arguments = parse_arguments()
    random.seed(arguments.seed)

    if arguments.config is not None:
        profile_config_file = open(arguments.config)
        profile_config = json.load(profile_config_file)
    else:
        profile_config = None
    profile_config = CaseInsensitiveDict(profile_config)

    if arguments.forward_packet_number is not None:
        profile_config['PACKETS_MIN_NUMBER'] = arguments.forward_packet_number
        profile_config['PACKETS_MAX_NUMBER'] = arguments.forward_packet_number

    if arguments.reverse_packet_number is not None:
        profile_config['PACKETS_REV_MIN_NUMBER'] = arguments.reverse_packet_number
        profile_config['PACKETS_REV_MAX_NUMBER'] = arguments.reverse_packet_number

    profile_generator = ProfileGenerator(profile_config)

    with open(arguments.output, 'w') as profile_file:
        profile_generator.write_profile(profile_file)


if __name__ == '__main__':
    main()
