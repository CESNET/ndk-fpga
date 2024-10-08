#!/bin/python3

#############################################################################
# jtag_op_mgmt.py: script for management of JTAG-over-protocol communication
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
# Notes:
#   run this script with sudo permissions
#############################################################################

import argparse as ap
import subprocess as sp

import nfb


# find etherlink connection information
def find_etherlink_info():
    ss_prg    = sp.Popen(["ss", "-tlp"], stdout=sp.PIPE)
    ss_ports  = ss_prg.stdout.read().decode()
    records   = ss_ports.split('\n')
    conn_info = None
    for r in records:
        if "etherlink" in r:
            r_fields  = r.split()
            conn_info = r_fields[3].split(':')
    return conn_info


# identification strings
default_dev_path        = "/dev/nfb0"
default_etherlink_path  = "/usr/local/bin/etherlink"
default_jtagconfig_path = "/opt/intelFPGA_pro/21.4/qprogrammer/quartus/bin/jtagconfig"
jtag_op_ctrl_compatible = "cesnet,ofm,intel_jtag_op_ctrl"
pci_endpoint_path       = "/system/device/endpoint0"
pci_slot_str            = "pci-slot"

# parse arguments
parser = ap.ArgumentParser()
parser.add_argument("-d", "--device", help="Path to device [default: {}]".format(default_dev_path), metavar="path", default=default_dev_path)
parser.add_argument("-e", "--etherlink", help="Path to etherlink executable [default: {}]".format(default_etherlink_path), metavar="path", default=default_etherlink_path)
parser.add_argument("-j", "--jtagconfig", help="Path to jtagconfig executable [default: {}]".format(default_jtagconfig_path), metavar="path", default=default_jtagconfig_path)
args = parser.parse_args()

# open device and find pci slot number
try:
    dev = nfb.open(args.device)
except FileNotFoundError:
    print("ERROR: Cannot open device {}".format(args.device))
    exit(1)

pci_slot = dev.fdt.get_node(pci_endpoint_path).get_property(pci_slot_str).value

# find JTAG_OP_CLIENT component in the design
nodes = dev.fdt_get_compatible(jtag_op_ctrl_compatible)
if len(nodes) < 1:
    print("ERROR: Cannot find JTAG_OP_CLIENT component in the design")
    exit(1)

comp = nodes[0]
comp_addr_space = comp.get_property("reg")
comp_addr_start = comp_addr_space[0]
comp_addr_span  = comp_addr_space[1]

# try to find a running instance of etherlink application
# NOTE: in the current version, only one instance of the app (of JTAG_OP_CLIENT component in the design) is supported
conn_info = find_etherlink_info()

# start etherlink application
if conn_info is None:
    etherlink_bin = args.etherlink
    resource_path = "--uio-driver-path=/sys/bus/pci/devices/{}/resource0".format(pci_slot)
    start_address = "--start-address={}".format(hex(comp_addr_start))
    address_span  = "--address-span={}".format(hex(comp_addr_span))
    etherlink_prg = sp.Popen([etherlink_bin, resource_path, start_address, address_span])
    conn_info     = find_etherlink_info()
    if conn_info is None:
        print("ERROR: Cannot start etherlink application (make sure you're running the script with sudo privileges)")
        exit(1)
else:
    print("INFO: Found a running instance of etherlink [{}:{}]".format(conn_info[0], conn_info[1]))

# register the application to jtag server
jtagconfig_bin = args.jtagconfig
hardware_type  = "JTAG-over-protocol"
connection_url = "sti://localhost:0/intel/remote-debug/{}:{}/{}".format(conn_info[0], conn_info[1], 0)
jtagconfig_prg = sp.run([jtagconfig_bin, "--add", hardware_type, connection_url])

# give cleanup information to the user
print("INFO: Available jtag connections")
sp.run([jtagconfig_bin])
print("INFO: If everything went smoothly, you should see a JTAG-over-protocol option listed above (without any warnings)")
print("INFO: Be sure to remove the connection after you're done with debugging ('jtagconfig --remove <#>' where <#> is the JTAG-over-protocol option number)")
