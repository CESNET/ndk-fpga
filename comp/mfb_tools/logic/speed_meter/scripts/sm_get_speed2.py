#!/usr/bin/env python3

# This is a simple script that uses the Speed Meter python application to get and print the Speed meter's throughput speed

import argparse as ap
import nfb
import ofm.comp.mfb_tools.logic.speed_meter as speedmeter


parser = ap.ArgumentParser()
parser.add_argument("-d", "--device", help="Set the path to the NFB device", default="/dev/nfb0")
parser.add_argument("-t", "--type", help="Type of output speed, Gbps ('b') or pps ('p')", choices=["b", "p"], default="b")
parser.add_argument("-c", "--clear", help="Clear speed meters", action="store_true")
parser.add_argument("-s", "--app_string", help="Name of the FW application", choices=["minimal", "nic", "replicator"], default="minimal")
args = parser.parse_args()

dev = nfb.open(args.device)

cores_cnt = len(dev.fdt_get_compatible(f"cesnet,{args.app_string},app_core"))

speeds = [] # the speed measured by the speed meter in each of the App cores
speed_meters = [speedmeter.SpeedMeter(dev=dev, index=i) for i in range(cores_cnt)]
for sm in speed_meters:
    speed_bps, speed_pps = sm.get_speed()

    if args.type == "b":
        speeds.append(f"{speed_bps / 10**9:.2f}")
    else:
        speeds.append(f"{speed_pps:.0f}")

    if args.clear:
        sm.clear_data()

units = "Gbps" if args.type == "b" else "pps"

for i, s in enumerate(speeds):
    print(f"Speed meter {i}: {s} {units}")
