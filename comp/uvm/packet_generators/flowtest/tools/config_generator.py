#!/bin/python3

# config_generator.py: Generator for FlowTest ft-generator (https://github.com/CESNET/FlowTest/tree/main/tools/ft-generator) config
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

# SPDX-License-Identifier: BSD-3-Clause

import yaml
import json
import argparse
import time
import random
import ipaddress
from typing import Optional
from requests.structures import CaseInsensitiveDict


class ConfigGenerator:

    ### PARAMETERS ###

    # Layer parameters.
    LAYER_MAX_NUMBER = 4
    LAYER_TYPES = [
        'vlan',
        'mpls'
    ]

    # Encapsulation parameters.
    ENCAPSULATION_ELEMENT_MAX_NUMBER = 10

    # Generated address numbers.
    # Disabled by default. It uses sequence-generated addresses that are passed in arguments.
    GENERATED_IPv4_RANGE_MAX_NUMBER = 0
    GENERATED_IPv6_RANGE_MAX_NUMBER = 0
    GENERATED_MAC_RANGE_MAX_NUMBER = 0

    # IPv4 prefix range.
    IPv4_PREFIX_MIN = 16
    IPv4_PREFIX_MAX = 32

    IPv4_MIN_PACKET_SIZE_TO_FRAGMENT_MIN = 512
    IPv4_MIN_PACKET_SIZE_TO_FRAGMENT_MAX = 512 * 3

    # IPv6 prefix range.
    IPv6_PREFIX_MIN = 64
    IPv6_PREFIX_MAX = 128

    IPv6_MIN_PACKET_SIZE_TO_FRAGMENT_MIN = 512
    IPv6_MIN_PACKET_SIZE_TO_FRAGMENT_MAX = 512 * 3

    # MAC prefix range.
    MAC_PREFIX_MIN = 24
    MAC_PREFIX_MAX = 48

    # Packet parameters.
    PACKET_MIN_SIZE = 60
    PACKET_MAX_SIZE = 1500
    PACKET_SIZE_MIN_STEP = 10
    PACKET_SIZE_MAX_STEP = 200

    # Other parameters.
    MAX_FLOW_INTER_PACKET_GAP = None

    # Mandatory address ranges.
    MANDATORY_IPv4_ADDRESS_RANGES = []
    MANDATORY_IPv6_ADDRESS_RANGES = []
    MANDATORY_MAC_ADDRESS_RANGES = []

    ### INITIALIZING ###

    def __init__(self, config: Optional[CaseInsensitiveDict] = None) -> None:
        self.actual_packet_size_max_probability = self.PACKET_MIN_SIZE
        #HOTFIX: this fix round error in FlowTest generator
        self.total_layers_probability = 99
        #self.total_layers_probability = 100

        if config is not None:
            self.__apply_config(config)

    def __apply_config(self, config: CaseInsensitiveDict) -> None:
        parameters = [attribute for attribute in dir(self) if attribute[0].isupper()] # Gets only parameters (e.g. PACKET_MIN_SIZE)
        for parameter in parameters:
            if parameter in config:
                self.__dict__[parameter] = config[parameter]

    ### ENCAPSULATION GENERATION ###

    def __generate_layer(self, layer_posible_typed: list) -> dict:
        layer = {}
        if len(layer_posible_typed) != 1:
            type = random.choices(layer_posible_typed, weights=[5, 3], # In purpose of evenly distributed protocol headers.
                                  k=1)
            type = type.pop()
        else:
            type = layer_posible_typed[0]

        layer['type'] = type

        if type == 'vlan':
            layer['id'] = random.randint(1, 4095)
        elif type == 'mpls':
            layer['label'] = random.randint(0, pow(2, 20) - 1)

            if layer_posible_typed.count('vlan') != 0: # VLAN cannot follow MPLS.
                layer_posible_typed.remove('vlan')

        return layer

    def __generate_layers(self) -> list:
        layers = []
        layer_posible_typed = self.LAYER_TYPES.copy()

        layer_number = random.randint(1, self.LAYER_MAX_NUMBER)
        for i in range(layer_number):
            layer = self.__generate_layer(layer_posible_typed)
            layers.append(layer)

        return layers

    def __generate_encapsulation_element(self) -> Optional[dict]:
        encapsulation_element = {}

        encapsulation_element['layers'] = self.__generate_layers()

        probability = random.randint(0, self.total_layers_probability)
        if probability == 0: # The encapsulation element with 0 probability of generation is useless.
            return None
        encapsulation_element['probability'] = str(probability) + '%'
        self.total_layers_probability = self.total_layers_probability - probability

        return encapsulation_element

    def __generate_encapsulation(self) -> list:
        encapsulation = []

        encapsulation_element_number = random.randint(1, self.ENCAPSULATION_ELEMENT_MAX_NUMBER)
        for i in range(encapsulation_element_number):
            encapsulation_element = self.__generate_encapsulation_element()
            if encapsulation_element is not None:
                encapsulation.append(encapsulation_element)

        return encapsulation

    ### IPv4 GENERATION ###

    def __generate_ipv4_address(self) -> str:
        return str(ipaddress.IPv4Address(random.randint(0, pow(2, 32) - 1))) + '/' + str(random.randint(self.IPv4_PREFIX_MIN, self.IPv4_PREFIX_MAX))

    def __generate_ipv4_range(self) -> list:
        ipv4_range = self.MANDATORY_IPv4_ADDRESS_RANGES.copy()

        ipv4_range_number = random.randint(0, self.GENERATED_IPv4_RANGE_MAX_NUMBER)
        for i in range(ipv4_range_number):
            ipv4 = self.__generate_ipv4_address()
            ipv4_range.append(ipv4)

        return ipv4_range

    def __generate_ipv4(self) -> dict:
        ipv4 = {}

        fragmentation_probability = random.randint(0, 100)
        ipv4['fragmentation_probability'] = str(fragmentation_probability) + '%'

        ipv4['min_packet_size_to_fragment'] = random.randint(self.IPv4_MIN_PACKET_SIZE_TO_FRAGMENT_MIN, self.IPv4_MIN_PACKET_SIZE_TO_FRAGMENT_MAX)

        ipv4_range = self.__generate_ipv4_range()
        if len(ipv4_range) != 0:
            ipv4['ip_range'] = ipv4_range

        return ipv4

    ### IPv6 GENERATION ###

    def __generate_ipv6_address(self) -> str:
        return str(ipaddress.IPv6Address(random.randint(0, pow(2, 128) - 1))) + '/' + str(random.randint(self.IPv6_PREFIX_MIN, self.IPv6_PREFIX_MAX))

    def __generate_ipv6_range(self):
        ipv6_range = self.MANDATORY_IPv6_ADDRESS_RANGES.copy()

        ipv6_range_number = random.randint(0, self.GENERATED_IPv6_RANGE_MAX_NUMBER)
        for i in range(ipv6_range_number):
            ipv6 = self.__generate_ipv6_address()
            ipv6_range.append(ipv6)

        return ipv6_range

    def __generate_ipv6(self) -> dict:
        ipv6 = {}

        fragmentation_probability = random.randint(0, 100)
        ipv6['fragmentation_probability'] = str(fragmentation_probability) + '%'

        ipv6['min_packet_size_to_fragment'] = random.randint(self.IPv6_MIN_PACKET_SIZE_TO_FRAGMENT_MIN, self.IPv6_MIN_PACKET_SIZE_TO_FRAGMENT_MAX)

        ipv6_range = self.__generate_ipv6_range()
        if len(ipv6_range) != 0:
            ipv6['ip_range'] = ipv6_range

        return ipv6

    ### MAC GENERATION ###

    def __generate_mac_address(self) -> str:
        return (
            "%02x:%02x:%02x:%02x:%02x:%02x/%d" % # MAC address format.
            (
                random.randint(0, 255),
                random.randint(0, 255),
                random.randint(0, 255),
                random.randint(0, 255),
                random.randint(0, 255),
                random.randint(0, 255),
                random.randint(self.MAC_PREFIX_MIN, self.MAC_PREFIX_MAX)
            )
        )

    def __generate_mac_range(self) -> list:
        mac_range = self.MANDATORY_MAC_ADDRESS_RANGES.copy()

        mac_range_number = random.randint(0, self.GENERATED_MAC_RANGE_MAX_NUMBER)
        for i in range(mac_range_number):
            mac = self.__generate_mac_address()
            mac_range.append(mac)

        return mac_range

    def __generate_mac(self) -> dict:
        mac = {}

        mac_range = self.__generate_mac_range()
        if len(mac_range) != 0:
            mac['mac_range'] = mac_range

        return mac

    ### PACKET SIZE PROBABILITIES GENERATION ###

    def __generate_packet_size_bounds(self) -> str:
        lower_bound = self.actual_packet_size_max_probability + 1
        upper_bound = random.randint(lower_bound + self.PACKET_SIZE_MIN_STEP, lower_bound + min(self.PACKET_SIZE_MAX_STEP, self.PACKET_MAX_SIZE - lower_bound))
        self.actual_packet_size_max_probability = upper_bound
        packet_size_bounds = f'{lower_bound}-{upper_bound}'

        return packet_size_bounds

    def __generate_packet_size_probabilities(self) -> dict:
        packet_size_probabilities = {}

        while (self.PACKET_MAX_SIZE - self.actual_packet_size_max_probability) > self.PACKET_SIZE_MIN_STEP:
            packet_size_bounds = self.__generate_packet_size_bounds()
            packet_size_probabilities[packet_size_bounds] = random.random()

        return packet_size_probabilities

    ### CONFIG GENERATION ###

    def generate(self) -> dict:
        config = {}

        config['encapsulation'] = self.__generate_encapsulation()
        config['ipv4'] = self.__generate_ipv4()
        config['ipv6'] = self.__generate_ipv6()

        mac = self.__generate_mac()
        if len(mac) != 0:
            config['mac'] = mac

        config['packet_size_probabilities'] = self.__generate_packet_size_probabilities()

        if self.MAX_FLOW_INTER_PACKET_GAP is not None:
            config['max_flow_inter_packet_gap'] = self.MAX_FLOW_INTER_PACKET_GAP

        return config

### MANDATORY ADDRESSES PROCESSING ###


def extend_list_attribute(dictionary: dict, attribute: str, value: list) -> None:
    if attribute in dictionary:
        dictionary[attribute].extend(value)
    else:
        dictionary[attribute] = value


def add_ipv4_from_arguments(config: dict, ipv4_string: str) -> None:
    ipv4_addresses_from_arguments = ipv4_string.split(';')
    extend_list_attribute(config, 'MANDATORY_IPv4_ADDRESS_RANGES', ipv4_addresses_from_arguments)


def add_ipv6_from_arguments(config: dict, ipv6_string: str) -> None:
    ipv6_addresses_from_arguments = ipv6_string.split(';')
    extend_list_attribute(config, 'MANDATORY_IPv6_ADDRESS_RANGES', ipv6_addresses_from_arguments)


def add_mac_from_arguments(config: dict, mac_string: str) -> None:
    mac_addresses_from_arguments = mac_string.split(';')
    extend_list_attribute(config, 'MANDATORY_MAC_ADDRESS_RANGES', mac_addresses_from_arguments)

### ARGUMENT PARSING ###


def parse_arguments() -> argparse.Namespace:
    argument_parser = argparse.ArgumentParser()

    argument_parser.add_argument('-o', '--output', type=str, help='Output file for generated config.', required=True)
    argument_parser.add_argument('-s', '--seed', type=int, help='Seed for randomization.', default=int(time.time() * 1000))
    argument_parser.add_argument('-c', '--config', type=str, help='Input configuration json file.', default=None)
    argument_parser.add_argument('--ipv4', type=str, help='IPv4 addresses in format \"addr1/mask1;addr2/mask2;addr3/mask3\".', default=None)
    argument_parser.add_argument('--ipv6', type=str, help='IPv6 addresses in format \"addr1/mask1;addr2/mask2;addr3/mask3\".', default=None)
    argument_parser.add_argument('--mac', type=str, help='MAC addresses in format \"addr1/mask1;addr2/mask2;addr3/mask3\".', default=None)

    arguments = argument_parser.parse_args()
    return arguments

### MAIN ###


def main() -> None:
    arguments = parse_arguments()
    random.seed(arguments.seed)

    if arguments.config is not None:
        generator_config_file = open(arguments.config)
        generator_config = json.load(generator_config_file)
    else:
        generator_config = None
    generator_config = CaseInsensitiveDict(generator_config)

    if arguments.ipv4 is not None:
        add_ipv4_from_arguments(generator_config, arguments.ipv4)
    if arguments.ipv6 is not None:
        add_ipv6_from_arguments(generator_config, arguments.ipv6)
    if arguments.mac is not None:
        add_mac_from_arguments(generator_config, arguments.mac)

    config_generator = ConfigGenerator(generator_config)
    config = config_generator.generate()

    with open(arguments.output, 'w') as config_file:
        yaml.dump(config, config_file, default_flow_style=False)


if __name__ == '__main__':
    main()
