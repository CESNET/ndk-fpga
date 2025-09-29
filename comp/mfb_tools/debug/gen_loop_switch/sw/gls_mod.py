#!/usr/bin/env python3
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import re
import subprocess
import time
import os
import csv
import signal
import socket
import datetime
import logging
import argparse
from typing import List, Optional
from dataclasses import dataclass
from tabulate import tabulate

import nfb
from ofm.comp.mfb_tools.debug.gen_loop_switch import GenLoopSwitch
from ofm.utils.units import convert_units


class GracefulExiter():
    """Graceful exit on SIGINT"""
    def __init__(self):
        self.state = False
        signal.signal(signal.SIGINT, self.change_state)

    def change_state(self, signum, frame):
        print("\nExit flag set to True")
        signal.signal(signal.SIGINT, signal.SIG_DFL)
        self.state = True

    def exit(self):
        return self.state


def stop_process(p: subprocess.Popen | None, timeout: float = 0.5) -> None:
    """Best-effort stop of a process group or single process."""
    if p is None:
        return
    if p.poll() is None: # process still runs
        try:
            # Try process group first
            pgid = os.getpgid(p.pid)
            os.killpg(pgid, signal.SIGINT)
        except ProcessLookupError:
            # Fallback to single process if process group not found
            p.send_signal(signal.SIGINT)
        time.sleep(0.2)
        if p.poll() is None: # still runs after SIGINT
            try:
                pgid = os.getpgid(p.pid)
                os.killpg(pgid, signal.SIGTERM)
            except ProcessLookupError:
                p.terminate()
        time.sleep(0.2)
        if p.poll() is None: # still runs after SIGTERM
            try:
                pgid = os.getpgid(p.pid)
                os.killpg(pgid, signal.SIGKILL)
            except ProcessLookupError:
                p.kill()
        p.wait(timeout=timeout) # reap the process (wait for child processs' exit status)


@dataclass
class GlsMuxConfig:
    r2l_gen: Optional[int]
    r2l_loop: Optional[int]
    l2r_gen: Optional[int]
    l2r_loop: Optional[int]


@dataclass
class TestModeSpec:
    desc: str
    mux_cfg: GlsMuxConfig
    gen_rev_chan: bool
    tx_sm: Optional[int] # None means it does not matter which one of the two will be used
    rx_sm: Optional[int] # None means it does not matter which one of the two will be used
    eth_loop: bool
    ndp_read: bool


@dataclass
class GlsInternals:
    gen: Optional[nfb.BaseComp]
    tx_sm: Optional[nfb.BaseComp]
    rx_sm: Optional[nfb.BaseComp]


# ==============================================================================
# The main TEST FUNCTION
# ==============================================================================

def run_test(
    gls_internals : List[GlsInternals],
    mode : str,
    fr_sizes : List[int],
    gls_clk_freq : int,
    log_en : bool,
    demo_en : bool,
    global_chan_range : str,
    rate_layer : int,
    cycles : int,
    report_name: str,
    device : int,
    exiter : GracefulExiter,
) -> None:

    demo_path = "/tmp/demo_gui.txt"
    ndp_gen = None

    if log_en:
        csv_name = "./report_" + report_name + ".csv"
        # Open CSV file to save data
        f = open(csv_name, "w", newline="")
        writer = csv.writer(f)

        # CSV file row
        row = ["Length", "TX APP speed", "RX APP speed"]
        writer.writerow(row)

    if mode in ["tx", "rxtx", "dma_tx", "dma_rxtx", "dma_loop"]:
        use_ndp_gen = True
    else:
        use_ndp_gen = False

    try:
        for length in fr_sizes:

            if exiter.exit():
                return

            # FW adds CRC to frame in ETH IP, generate smaller frames
            gen_length = length - 4

            if rate_layer == 2:
                print(f"Frame Size (with CRC):     {length} [Bytes]")
            else:
                length = length + 8 + 12
                print(f"Frame Size (with preamble, SFD, CRC, and IPG):  {length} [Bytes]")
            print("----------------------------------------")

            # Start generating traffic
            if use_ndp_gen:
                ndp_gen = subprocess.Popen(
                    f"ndp-generate -d {device} -s {gen_length} -i {global_chan_range}",
                    shell=True,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    start_new_session=True, # spawns new session / process group
                )
            for g in gls_internals:
                if g.gen is not None:
                    g.gen.frame_length = gen_length
                    g.gen.enabled = True

            time.sleep(0.5)
            tx_total_speed = 0
            rx_total_speed = 0

            for i, g in enumerate(gls_internals):
                print("Data Stream: " + str(i))
                tx_app_speed = 0
                rx_app_speed = 0

                for _ in range(cycles):
                    if g.tx_sm is not None:
                        g.tx_sm.clear_data()
                        tx_speed = g.tx_sm.measure(f=gls_clk_freq)[0]
                    else:
                        tx_speed = 0
                    if g.rx_sm is not None:
                        g.rx_sm.clear_data()
                        rx_speed = g.rx_sm.measure(f=gls_clk_freq)[0]
                    else:
                        rx_speed = 0

                    tx_app_speed += tx_speed
                    rx_app_speed += rx_speed

                tx_app_speed = round((tx_app_speed/cycles), 2)
                rx_app_speed = round((rx_app_speed/cycles), 2)

                # Adjust speed according to the actual frame size based on the layer (L1 or L2)
                fix = (length) / (gen_length)
                tx_app_speed = tx_app_speed * fix
                rx_app_speed = rx_app_speed * fix

                tx_app_speed_conv, tx_units = convert_units(tx_app_speed)
                rx_app_speed_conv, rx_units = convert_units(rx_app_speed)
                print(f"Stream Speed TX:          {tx_app_speed_conv:7.2f} [{tx_units}bps]")
                print(f"Stream Speed RX:          {rx_app_speed_conv:7.2f} [{rx_units}bps]")
                print("----------------------------------------")

                tx_total_speed += tx_app_speed
                rx_total_speed += rx_app_speed

            tx_total_speed = round(tx_total_speed, 2)
            rx_total_speed = round(rx_total_speed, 2)

            tx_total_speed_conv, tx_units = convert_units(tx_app_speed)
            rx_total_speed_conv, rx_units = convert_units(rx_app_speed)

            # Total => all ports added together
            print(f"Total Speed TX:           {tx_total_speed_conv:7.2f} [{tx_units}bps]")
            print(f"Total Speed RX:           {rx_total_speed_conv:7.2f} [{rx_units}bps]")
            print("========================================")

            if demo_en:
                with open(demo_path, "w") as demo_gui:
                    demo_gui.write(str(length) + "\n")
                    demo_gui.write(str(tx_total_speed) + "\n")
                    demo_gui.write(str(rx_total_speed))

            # Stop generating traffic
            if ndp_gen is not None:
                stop_process(ndp_gen)
                ndp_gen = None
            for g in gls_internals:
                if g.gen is not None:
                    g.gen.enabled = False

            time.sleep(0.1)

            if log_en:
                # Save row to CSV file
                row = [str(length), str(tx_total_speed), str(rx_total_speed)]
                writer.writerow(row) # write data to CSV file

    finally:
        stop_process(ndp_gen)
        if log_en:
            try:
                f.close()
            except Exception:
                pass
        if demo_en:
            try:
                os.remove(demo_path)
            except FileNotFoundError:
                pass


# ==============================================================================
# GLS HELP FUNCTIONs
# ==============================================================================

def parse_range_arg(arg: str | None, max_value: int, default: str = "0") -> List[int]:
    """Parse a string argument representing a list/range of integers.

    Args:
        arg: The input string to parse. If None, the value of the `default` param is used.
        max_value: The maximum value for the range; used when arg is "-1".
        default: The default value assigned to the `arg` param if it is None.

    Returns:
        A list of integers parsed from the input string.

    Raises:
        ValueError: If the input string is invalid.

    Examples:
        "0,1,2-5,7" -> [0, 1, 2, 3, 4, 5, 7]
        "-1" -> list(range(0, max_value))
        None -> [int(default)]
    """
    if arg is None:
        arg = default
    if arg == "-1":
        return list(range(0, max_value))
    items = arg.split(",")
    result = []
    for item in items:
        if "-" in item:
            lo_idx, hi_idx = item.split("-")
            result.extend(list(range(int(lo_idx), int(hi_idx)+1)))
        else:
            result.append(int(item))
    return result


# ==============================================================================
# GLS MAIN FUNCTION
# ==============================================================================

def main():

    logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.INFO)

    modes = {
        "eth_gen":  TestModeSpec(
                        desc="HW Gen --> TX ETH     ==> RX ETH --> Black Hole; (ETH loopback)",
                        mux_cfg=GlsMuxConfig(r2l_gen=1, r2l_loop=0, l2r_gen=1, l2r_loop=0),
                        gen_rev_chan=False,
                        tx_sm=1,
                        rx_sm=2,
                        eth_loop=True,
                        ndp_read=False,
                    ),
        "rx":       TestModeSpec(
                        desc="HW Gen --> TX ETH     ==> RX ETH --> RX DMA;     (ETH loopback)",
                        mux_cfg=GlsMuxConfig(r2l_gen=1, r2l_loop=0, l2r_gen=0, l2r_loop=0),
                        gen_rev_chan=False,
                        tx_sm=1,
                        rx_sm=0,
                        eth_loop=True,
                        ndp_read=True,
                    ),
        "tx":       TestModeSpec(
                        desc="TX DMA --> TX ETH     ==> RX ETH --> Black Hole; (ETH loopback)",
                        mux_cfg=GlsMuxConfig(r2l_gen=0, r2l_loop=0, l2r_gen=1, l2r_loop=0),
                        gen_rev_chan=False,
                        tx_sm=1, # Both (1 or 3) can be used
                        rx_sm=2,
                        eth_loop=True,
                        ndp_read=False,
                    ),
        "rxtx":     TestModeSpec(
                        desc="TX DMA --> TX ETH     ==> RX ETH --> RX DMA;     (ETH loopback)",
                        mux_cfg=GlsMuxConfig(r2l_gen=0, r2l_loop=0, l2r_gen=0, l2r_loop=0),
                        gen_rev_chan=False,
                        tx_sm=1, # Both (1 or 3) can be used
                        rx_sm=0, # Both (0 or 2) can be used
                        eth_loop=True,
                        ndp_read=True,
                    ),
        "dma_rx":   TestModeSpec(
                        desc="HW Gen --> RX DMA     ###",
                        mux_cfg=GlsMuxConfig(r2l_gen=None, r2l_loop=None, l2r_gen=1, l2r_loop=0),
                        gen_rev_chan=False, # Setting this true may have positive impact on performance
                        tx_sm=None, # Speed Meter not used
                        rx_sm=0,
                        eth_loop=False,
                        ndp_read=True,
                    ),
        "dma_tx":   TestModeSpec(
                        desc="TX DMA --> Black Hole ###",
                        mux_cfg=GlsMuxConfig(r2l_gen=1, r2l_loop=None, l2r_gen=None, l2r_loop=None),
                        gen_rev_chan=False,
                        tx_sm=3,
                        rx_sm=None, # Speed Meter not used
                        eth_loop=False,
                        ndp_read=False,
                    ),
        "dma_rxtx": TestModeSpec(
                        desc="TX DMA --> Black Hole ### HW Gen --> RX DMA;",
                        mux_cfg=GlsMuxConfig(r2l_gen=1, r2l_loop=None, l2r_gen=1, l2r_loop=0),
                        gen_rev_chan=False, # Setting this true may have positive impact on performance
                        tx_sm=3,
                        rx_sm=0,
                        eth_loop=False,
                        ndp_read=True,
                    ),
        "dma_loop": TestModeSpec(
                        desc="TX DMA --> RX DMA     ### (internal DMA loopback)",
                        mux_cfg=GlsMuxConfig(r2l_gen=1, r2l_loop=None, l2r_gen=None, l2r_loop=1),
                        gen_rev_chan=False,
                        tx_sm=3,
                        rx_sm=0,
                        eth_loop=False,
                        ndp_read=True,
                    ),
    }

    modes_table = tabulate([(k, v.desc) for k, v in modes.items()], tablefmt="grid")

    help_dict = {
        "device"    : "set the target device; default: 0 (/dev/nfb0)",
        "index"     : "select index(es) of GLS in the Device Tree, e.g.: 0,1; -1 = all available; default: 0",
        "log"       : "enable logging to a CSV file",
        "demo"      : "enable for demo - logs to a TXT file in /tmp directory",
        "mode"      : "set the test mode; options:\n" + modes_table,
        "channels"  : "select the range of Channels used in the test in 'min-max' format; default = all available",
        "size"      : "set the frame size(s) in bytes; MIN must be >= 64, MAX <= 1518, STEP >= 1; default: 64 1518 16",
        "repeat"    : "repeat the test until interrupted, otherwise it runs only once",
        "loopback"  : "force using external loopback instead of PMA loopback (default, only for some modes)",
        "cycles"    : "set the number of test cycles that are averaged for each frame length, default: 4",
        "frequency" : "set the clock frequency [Hz] at which the APP Core runs; default: 200_000_000",
        "layer"     : "measure the rate at ISO/OSI layer: 1 or 2; default: 2",
    }

    gls_desc = """
        Uses the GEN_LOOP_SWITCH (SW+FW) module to perform throughput measurements.
    """

    arg_parser = argparse.ArgumentParser(
        prog="gls_mod.py",
        description=gls_desc,
        formatter_class=argparse.RawTextHelpFormatter,
    )

    arg_parser.add_argument("-d", "--device", default=nfb.default_dev_path, help=help_dict["device"])
    arg_parser.add_argument("-i", "--index", nargs="?", default="0", help=help_dict["index"])
    arg_parser.add_argument("-l", "--log", action="store_true", help=help_dict["log"])
    arg_parser.add_argument("-L", "--log_demo", action="store_true", help=help_dict["demo"])
    arg_parser.add_argument("-m", "--mode", required=True, choices=modes.keys(), help=help_dict["mode"])
    arg_parser.add_argument("-c", "--channels", help=help_dict["channels"])
    arg_parser.add_argument("-s", "--frame_size", nargs=3, metavar=("MIN", "MAX", "STEP"), help=help_dict["size"])
    arg_parser.add_argument("-R", "--repeat", action="store_true", help=help_dict["repeat"])
    arg_parser.add_argument("-e", "--ext_loop", action="store_true", help=help_dict["loopback"])
    arg_parser.add_argument("-C", "--test_cycles", type=int, default=4, help=help_dict["cycles"])
    arg_parser.add_argument("-f", "--frequency", type=int, default=200_000_000, help=help_dict["frequency"])
    arg_parser.add_argument("-r", "--rate_layer", type=int, default=2, choices=[1, 2], help=help_dict["layer"])
    args = arg_parser.parse_args()

    device = nfb.open(args.device)

    sel_mode = modes[args.mode]

    if args.frame_size:
        try:
            min_fr_size = int(args.frame_size[0])
            max_fr_size = int(args.frame_size[1])
            fr_size_step = int(args.frame_size[2])
        except ValueError as exc:
            raise ValueError("ERROR: Invalid frame_size parameter! See help for details.") from exc
        if min_fr_size < 64 or max_fr_size > 1518 or fr_size_step < 1:
            raise ValueError("ERROR: Invalid frame_size parameter! See help for details.")
        fr_sizes = list(range(min_fr_size, max_fr_size+1, fr_size_step))
    else:
        fr_sizes = list(range(64, 1518+1, 16))

    # ==========================================================================
    # TEST CONFIGURATION
    # ==========================================================================

    # Enable RX DMA
    ndp_read = None
    if sel_mode.ndp_read:
        pname = f"ndp-read -d {args.device}"
        ndp_read = subprocess.Popen(
            pname,
            shell=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            start_new_session=True, # spawns new session / process group
        )
        logging.info(f"Enabled RX DMA ({pname})")

    logging.info("Finding information about NDK firmware...")
    fdt_firmware = nfb.Nfb(args.device).fdt.get_node("firmware")
    card_name = fdt_firmware.get_property("card-name").value
    logging.info(f"Card name:      {card_name}")

    # Total number of Ethernet ports on card
    eth_ports = len(list(device.eth))
    logging.info(f"APP streams:    {eth_ports}")

    # Find GLS modules in the Device Tree
    gls_count = 0
    pattern = re.compile(r"^dbg_gls(\d+)$")
    fdt_mi_pci0_bar0 = fdt_firmware.get_subnode("mi_pci0_bar0")
    for node in fdt_mi_pci0_bar0.nodes:
        if re.search(pattern, node.name):
            gls_count += 1
    logging.info(f"GLS modules:    {gls_count}")
    if (gls_count == 0):
        raise RuntimeError("ERROR: Unsupported NDK firmware, no GLS modules found!")
    elif (gls_count > eth_ports) or (gls_count < eth_ports and gls_count != 1):
        raise RuntimeError("ERROR: Unsupported NDK firmware, unsupported configuration of GLS modules or ETH ports!")

    # Get total number of DMA channels
    rx_queues = device.ndp.rx
    tx_queues = device.ndp.tx
    dma_chan_rx = len(rx_queues)
    dma_chan_tx = len(tx_queues)
    logging.info(f"DMA RX queues:  {dma_chan_rx}")
    logging.info(f"DMA TX queues:  {dma_chan_tx}")
    if (dma_chan_rx != dma_chan_tx):
        raise RuntimeError("ERROR: Unsupported NDK firmware, the number of RX and TX DMA queues must be the same!")

    dma_channels = dma_chan_rx

    # NO DMA hotfix
    if dma_channels == 0:
        logging.warning("No DMA channels found, defaulting to 8 as a hotfix for no-DMA configuration.")
        dma_channels = gls_count*8

    # Process selected channels argument
    if args.channels:
        if "-" in args.channels:
            try:
                sel_channel_min_str, sel_channel_max_str = args.channels.split("-")
            except ValueError as exc:
                raise ValueError("ERROR: Invalid channel range selection! See help for details.") from exc
            try:
                sel_channel_min = int(sel_channel_min_str)
                sel_channel_max = int(sel_channel_max_str)
            except ValueError as exc:
                raise ValueError("ERROR: Invalid channel range selection! See help for details.") from exc
            if sel_channel_min < 0 or sel_channel_min > sel_channel_max:
                raise ValueError("ERROR: Invalid channel range selection! See help for details.")
            if sel_channel_max >= dma_channels:
                raise ValueError(f"ERROR: Invalid channel range selection! Available channels: {dma_channels}.")
            if sel_channel_min == sel_channel_max:
                full_chan_range = str(sel_channel_min)
            else:
                full_chan_range = f"{sel_channel_min}-{sel_channel_max}"
        else:
            try:
                sel_channel_min = int(args.channels)
            except ValueError as exc:
                raise ValueError("ERROR: Invalid channel selection! See help for details.") from exc
            if sel_channel_min < 0 or sel_channel_min >= dma_channels:
                raise ValueError(f"ERROR: Invalid channel selection! Available channels: {dma_channels}.")
            sel_channel_max = sel_channel_min
            full_chan_range = args.channels
    else:
        sel_channel_min = 0
        sel_channel_max = dma_channels - 1
        full_chan_range = f"{sel_channel_min}-{sel_channel_max}"

    # Generate Channel range (min-max values) per each GLS Generator according to the selection.
    # For l2r Generators (to RX DMA), it is not neccessary to restrict the chanel range like this.
    # Instead, the full selected channel range could be applied to the l2r Generator of each GLS module.
    channels_per_stream = dma_channels // gls_count
    gls_operated_channels = []
    sel_chan_ranges = []
    for i in range(gls_count):
        stream_min = i * channels_per_stream
        stream_max = (i + 1) * channels_per_stream - 1
        gls_operated_channels.append(f"{stream_min}-{stream_max}")
        # Decide per GLS if there is an overlap with the selected channel range
        overlap_min = max(stream_min, sel_channel_min)
        overlap_max = min(stream_max, sel_channel_max)
        if overlap_min <= overlap_max:
            sel_chan_ranges.append((overlap_min-stream_min, overlap_max-stream_min))
        else:
            sel_chan_ranges.append(None)

    gls_chan_range_list = list(zip(range(gls_count), gls_operated_channels))
    gls_chan_range_table = tabulate(gls_chan_range_list, headers=["GLS Module Index", "Available Channels"], tablefmt="grid")
    logging.info(f"GLS Modules Channel Ranges:\n{gls_chan_range_table}")
    logging.info(f"Selected Channel Range: {full_chan_range}")

    # GLS modules instantiation and configuration
    try:
        gls_idx_list = parse_range_arg(args.index, gls_count)
    except ValueError as exc:
        raise ValueError("ERROR: Failed to parse GLS instance selection! See help for details.") from exc
    logging.info(f"Selected GLS instance(s): {','.join(map(str, gls_idx_list))}")
    gls_internals_list = []
    for i in gls_idx_list:
        try:
            gls = GenLoopSwitch(dev=device, index=i)
        except IndexError as exc:
            raise ValueError(f"ERROR: GLS module at index {i} not available!") from exc

        # Select and configure the generator according to the selected mode
        if args.mode in ["eth_gen", "rx"]:
            gls_gen = gls.r2l.gen
        elif args.mode in ["dma_rx", "dma_rxtx"]:
            gls_gen = gls.l2r.gen
        else:
            gls_gen = None

        if sel_chan_ranges[i] is not None:
            if gls_gen is not None: # gls_gen only exists in some modes
                gls_gen.minimum_channel = sel_chan_ranges[i][0]
                gls_gen.maximum_channel = sel_chan_ranges[i][1]
                # gls_gen.channel_increment = ...
                gls_gen.channel_increment_reversed = sel_mode.gen_rev_chan
        else:
            raise RuntimeError(f"ERROR: No selected channels overlap with the available channels of Generator at GLS {i}!")

        # Configure the four GLS MUXes according to the selected mode
        gls_mux_cfg = sel_mode.mux_cfg
        if gls_mux_cfg.r2l_gen is not None:
            gls.r2l.mux_generator = gls_mux_cfg.r2l_gen
        if gls_mux_cfg.r2l_loop is not None:
            gls.r2l.mux_loopback = gls_mux_cfg.r2l_loop
        if gls_mux_cfg.l2r_gen is not None:
            gls.l2r.mux_generator = gls_mux_cfg.l2r_gen
        if gls_mux_cfg.l2r_loop is not None:
            gls.l2r.mux_loopback = gls_mux_cfg.l2r_loop

        # Get TX and RX Speed Meters according to the selected mode
        match sel_mode.tx_sm:
            case 1: gls_tx_sm = gls.r2l.tx_sm
            case 3: gls_tx_sm = gls.r2l.rx_sm
            case _: gls_tx_sm = None
        match sel_mode.rx_sm:
            case 0: gls_rx_sm = gls.l2r.tx_sm
            case 2: gls_rx_sm = gls.l2r.rx_sm
            case _: gls_rx_sm = None
        gls_internals_list.append(
            GlsInternals(
                gen=gls_gen,
                tx_sm=gls_tx_sm,
                rx_sm=gls_rx_sm,
            )
        )

    # Reset Ethernet stats and enable MACs (and potentionally PMA loopback)
    for e in device.eth:
        e.stats_reset()
        e.enable()
        if not args.ext_loop and sel_mode.eth_loop:
            e.pcspma.pma_local_loopback = True

    # Reset DMA stats
    for q in rx_queues:
        q.stats_reset()
    for q in tx_queues:
        q.stats_reset()

    logging.info("Initial test setup completed.\n")

    # ==========================================================================
    # GLS TEST START
    # ==========================================================================

    x = 1
    exiter = GracefulExiter()
    while True:
        logging.info(f"Test #{x} started...")
        x += 1
        now = datetime.datetime.now()
        date_time = now.strftime("%Y-%m-%d_%H-%M-%S")
        host_name = socket.gethostname().partition(".")[0] # get short hostname without domain (.liberouter.org)
        report_name = host_name + "_" + card_name + "_" + args.mode + "_ch" + full_chan_range + "_" + date_time
        run_test(
            gls_internals=gls_internals_list,
            mode=args.mode,
            fr_sizes=fr_sizes,
            gls_clk_freq=args.frequency,
            log_en=args.log,
            demo_en=args.log_demo,
            global_chan_range=full_chan_range,
            rate_layer=args.rate_layer,
            cycles=args.test_cycles,
            report_name=report_name,
            device=args.device,
            exiter=exiter,
        )
        logging.info("Test finished.\n")
        if not args.repeat or exiter.exit():
            print("END: Exiting...")
            for gi in gls_internals_list:
                if gi.gen is not None:
                    gi.gen.enabled = False
            time.sleep(1.0)
            stop_process(ndp_read)
            break


if __name__ == "__main__":
    main()
