#!/usr/bin/env python3
# len_throughput_test.py: sweep the packet length and plot DRAM write throughput
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Adam Zatloukal <zatloukal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
"""Sweep the generated packet length and plot DRAM capture throughput against it.

Drives traffic with the Gen Loop Switch, reads the RX speed meter at each frame
length, and writes a CSV plus a SVG plot. Non-interactive - run it to characterise
how throughput varies with packet size. The --frame-size maximum must not exceed
16316 B or the GLS stops generating traffic.

Usage: ./len_throughput_test.py -s 64 1518 64 -o /tmp/sweep -v
"""

import argparse
import csv
import faulthandler
import os
import signal
import subprocess
import time
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import nfb  # noqa: E402
from ofm.comp.mfb_tools.debug.gen_loop_switch import GenLoopSwitch  # noqa: E402
from ofm.comp.mfb_tools.logic.speed_meter import SpeedMeter  # noqa: E402

from dram_pkt_capture_regs import AppStatus, RxMacRegs  # noqa: E402

# The TX MAC Lite appends the FCS, so ask the generator for 4 B less than the
# frame length we sweep over and report.
ETH_CRC_BYTES = 4

# The speed meters are built CNT_TICKS_WIDTH = 24 at 200 MHz, so a measurement
# window closes after 2**24 / 200e6 = 84 ms.
SM_WINDOW_S = 0.084

# Preamble + SFD (8 B) + interframe gap (12 B), for the line-rate overlay.
ETH_L1_OVERHEAD_BYTES = 20

PALETTE = ["#2a78d6", "#eb6834", "#1baf7a", "#eda100"]


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("-d", "--device", default=nfb.default_dev_path)
    ap.add_argument("-o", "--output", default="len_throughput",
                    help="output path prefix for the .csv and .svg")
    ap.add_argument("-s", "--frame-size", nargs=3, type=int, default=[64, 16304, 16],
                    metavar=("MIN", "MAX", "STEP"),
                    help="frame length sweep in bytes, incl. FCS (default: 64 16304 16)")
    ap.add_argument("-c", "--core", type=int, default=0,
                    help="which app core / GLS to sweep (default: 0); the cores "
                         "measure the same thing, so one is enough")
    ap.add_argument("-C", "--cycles", type=int, default=4,
                    help="speed meter windows averaged per length (default: 4)")
    ap.add_argument("-M", "--pkt-mtu", type=int, default=16383,
                    help="RX MAC maximum frame length (default: 16383)")
    ap.add_argument("-v", "--verbose", action="store_true",
                    help="print every speed-meter window and drain step")
    ap.add_argument("--drain-timeout", type=float, default=30.0,
                    help="give up emptying the DRAM after this many seconds (default: 30)")
    ap.add_argument("-r", "--eth-rate", type=float, default=None,
                    help="link rate in Gbps; overlays the theoretical line-rate limit")
    args = ap.parse_args()

    faulthandler.enable()
    faulthandler.register(signal.SIGUSR1)
    print(f"pid {os.getpid()} - if this stalls, run:  kill -USR1 {os.getpid()}")

    dev = nfb.open(args.device)

    node = dev.fdt_get_compatible("cesnet,dram_pkt_capture,app_core")[args.core]
    st = AppStatus(dev=dev, node=node.get_subnode("app_status"))
    rx = SpeedMeter(dev=dev, node=node.get_subnode("rx_speed_meter"))
    tx = SpeedMeter(dev=dev, node=node.get_subnode("tx_speed_meter"))

    for i in range(len(dev.fdt_get_compatible(RxMacRegs.DT_COMPATIBLE))):
        RxMacRegs(dev=dev, index=i).set_max_frame_len(args.pkt_mtu)

    for e in dev.eth:
        e.enable()
        e.pcspma.pma_local_loopback = True

    n_cores = len(dev.fdt_get_compatible("cesnet,dram_pkt_capture,app_core"))
    n_gls = len(dev.fdt_get_compatible(GenLoopSwitch.DT_COMPATIBLE))
    cores_per_gls = n_cores // n_gls            # 1 for Medusa, 2 for Calypte
    per_core = len(dev.ndp.tx) // n_cores

    gen = GenLoopSwitch(dev=dev, index=args.core // cores_per_gls).r2l
    gen.gen.minimum_channel = (args.core % cores_per_gls) * per_core
    gen.gen.maximum_channel = gen.gen.minimum_channel + per_core - 1

    # Something has to consume RX DMA or the DRAM cannot be drained between lengths.
    ndp_read = subprocess.Popen(["ndp-read", "-d", args.device],
                                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    lengths = list(range(args.frame_size[0], args.frame_size[1] + 1, args.frame_size[2]))
    # results[i] is the mean write throughput at lengths[i]
    results = [0.0] * len(lengths)
    t0 = time.time()

    csv_path = Path(args.output).with_suffix(".csv")
    csv_path.parent.mkdir(parents=True, exist_ok=True)
    csv_file = open(csv_path, "w", newline="")
    csv_w = csv.writer(csv_file)
    csv_w.writerow(["core", "length", "bps", "windows"])
    csv_file.flush()

    print(f"core {args.core} of {n_gls}, sweeping {len(lengths)} lengths")
    print(f"Writing {csv_path} as it goes\n")
    try:
        for point, length in enumerate(lengths):
            gen.gen_start(en_path=True, length=length - ETH_CRC_BYTES)
            st.set_read_enable(False)
            rx.clear_data()
            st.set_capture_enable(True)

            # Sample until the cycle budget runs out or this core's DRAM fills,
            samples = []
            for _ in range(args.cycles):
                time.sleep(SM_WINDOW_S)
                samples.append(rx.get_speed()[0])
                rx.clear_data()
                if args.verbose:
                    print(f"  SAMPLE:{samples[-1] / 1e9:>7.2f}G"
                          f"\tWR_EN:{st.capture_enable}")
                if not st.capture_enable:
                    break

            gen.gen_stop()

            # Average only the windows that carried traffic: the last one is cut
            # short when the DRAM fills, and averaging its zero in would drag
            # the reported rate down.
            live = [v for v in samples if v > 0]
            results[point] = sum(live) / len(live) if live else 0.0

            csv_w.writerow([args.core, length, f"{results[point]:.1f}", len(live)])
            csv_file.flush()

            elapsed = time.time() - t0
            print(f"[{point+1:>4}/{len(lengths)} {elapsed:6.0f}s] "
                  f"len {length:>5} B  {results[point] / 1e9:>7.2f}G  "
                  f"({len(live)}/{len(samples)} windows)")

            # Empty this core's DRAM so the next length gets a full buffer.
            st.set_read_enable(True)
            tx.clear_data()
            deadline = time.time() + args.drain_timeout
            idle = 0
            while time.time() < deadline:
                time.sleep(SM_WINDOW_S)
                rate = tx.get_speed()[0]
                tx.clear_data()
                if args.verbose:
                    print(f"  TX:{rate / 1e9:>7.2f}G"
                          f"\tFULL:{st.dram_full}")
                if rate == 0:
                    idle += 1
                    if idle >= 2:
                        break
                else:
                    idle = 0
            st.set_read_enable(False)
    finally:
        gen.gen_stop()
        st.set_capture_enable(False)
        st.set_read_enable(False)
        ndp_read.terminate()
        csv_file.close()

    print(f"\nSaved {csv_path}")

    x = lengths
    fig, ax = plt.subplots(figsize=(9, 5.5))
    ax.plot(x, [v / 1e9 for v in results], color=PALETTE[0],
            linewidth=1.6, label=f"Core {args.core}")
    if args.eth_rate:
        ax.plot(x, [args.eth_rate * b / (b + ETH_L1_OVERHEAD_BYTES) for b in x],
                color="#898781", linewidth=1, linestyle="--",
                label=f"{args.eth_rate}G line-rate limit")
    # A 64 B to 16 kB sweep crushes the interesting small-packet knee against the
    # left edge on a linear axis.
    if x and x[-1] / x[0] >= 8:
        ax.set_xscale("log")
        ticks = [t for t in (64, 128, 256, 512, 1024, 1518, 4096, 8192, 16383)
                 if x[0] <= t <= x[-1]]
        ax.set_xticks(ticks)
        ax.set_xticklabels([str(t) for t in ticks])
        ax.minorticks_off()
    ax.set_xlabel("Frame length [B]")
    ax.set_ylabel("Write throughput [Gb/s]")
    ax.set_title("DRAM capture throughput vs packet length", loc="left")
    ax.grid(True, color="#e1e0d9", linewidth=0.6)
    ax.set_axisbelow(True)
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    fig.tight_layout()
    svg_path = Path(args.output).with_suffix(".svg")
    fig.savefig(svg_path, dpi=150)
    print(f"Saved {svg_path}")


if __name__ == "__main__":
    main()
