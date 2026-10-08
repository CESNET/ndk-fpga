# throughput_test.py: script to sample & measure throughput of dram_pkt_capture application
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Adam Zatloukal <zatloukal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
"""Live RX/TX throughput monitor for a running dram_pkt_capture card.

Samples the RX and TX speed meters of every app core at a fixed interval and
prints a table of the results. Press 'w' to toggle capture_enable, 'r' to
toggle read_enable, Ctrl+C to stop. Use this to watch a capture fill the DRAM
ring and then drain it.

Generating & reading the traffic is up to the user.
For frame generation use GLS or ndp-generate.
For reading frames from DMA use ndp-read.
"""

import nfb
import ofm.comp.mfb_tools.logic.speed_meter as speedmeter
import time
import argparse
import threading
import sys
import termios
import tty

from dram_pkt_capture_regs import AppStatus, RxMacRegs


def main():

    def _key_watcher(app_status_list):
        """Toggle enables on key press: 'w' -> write enable, 'r' -> read enable"""
        while True:
            key = sys.stdin.read(1)
            if not key:  # EOF
                return
            key = key.lower()
            if key == "w":
                new = not app_status_list[0].capture_enable        # read current HW state
                for st in app_status_list:
                    st.set_capture_enable(new)
                print(f"\n>>> write_enable -> {new}")
            elif key == "r":
                new = not app_status_list[0].read_enable   # read current HW state
                for st in app_status_list:
                    st.set_read_enable(new)
                print(f"\n>>> read_enable -> {new}")

    parser = argparse.ArgumentParser(description="Measure throughput during DRAM packet capture")
    parser.add_argument("-d", "--device",
                        help="NFB device path",
                        default=nfb.default_dev_path)
    parser.add_argument("-t", "--sample-time",
                        type=float,
                        default=0.1,
                        help="Time between samples in seconds")
    parser.add_argument("-m", "--max-samples",
                        type=int,
                        default=1000,
                        help="Maximum number of samples (default: 1000)")
    parser.add_argument('-i', '--idle-threshold',
                        type=int,
                        default=100,
                        help='Number of consecutive idle samples to stop (default: 5)')

    args = parser.parse_args()

    dev = nfb.open(args.device)

    # Get status control registers
    app_status_list = [AppStatus(dev=dev, index=i) for i in range(len(dev.fdt_get_compatible(AppStatus.DT_COMPATIBLE)))]
    if not app_status_list:
        print("ERROR: No app_status component found!")
        return 1

    # Set RX MAC Lite maximal frame length
    pkt_mtu = 16383
    for i in range(len(dev.fdt_get_compatible(RxMacRegs.DT_COMPATIBLE))):
        RxMacRegs(dev=dev, index=i).set_max_frame_len(pkt_mtu)

    # Get number of cores
    cores_cnt = len(dev.fdt_get_compatible("cesnet,dram_pkt_capture,app_core"))
    print(f"Identified number of cores: {cores_cnt}")

    # Array of speed meter objects
    speed_meters = [speedmeter.SpeedMeter(dev=dev, index=i) for i in range(cores_cnt * 2)]

    print("Clearing speed meters...")
    for sm in speed_meters:
        sm.clear_data()

    # Enable capture
    print("Clearing speed meters...")
    for st in app_status_list:
        st.set_capture_enable(True)

    # Verify enable
    for i, st in enumerate(app_status_list):
        print(f"Capture enable register CORE[{i}]: {st.capture_enable}")

    print(f"\nSampling speed meters every {args.sample_time}s...")
    print("Press 'w' to toggle write_enable, 'r' to toggle read_enable, Ctrl+C to stop")
    header = f"{'Sample':>6} {'Time':>8}"
    header_group = f"{'RX':>9} {'TX':>9}  {'WR':^6}{'RD':^6}"
    enable_group = f"{'':19}  {'Enable':^12}"
    core_line = " " * len(header)
    enable_line = " " * len(header)
    for i in range(cores_cnt):
        core_line += f" | {'Core ' + str(i):^{len(header_group)}}"
        enable_line += f" | {enable_group}"
        header += f" | {header_group}"
    print(core_line)
    print(enable_line)
    print(header)
    print("-" * len(header))

    sample_count = 0
    idle_count = 0
    start_time = time.time()

    old_term = None
    if sys.stdin.isatty():
        old_term = termios.tcgetattr(sys.stdin)
        tty.setcbreak(sys.stdin)
    threading.Thread(target=_key_watcher, args=(app_status_list,), daemon=True).start()

    try:
        while sample_count < args.max_samples:
            sample_count += 1
            elapsed = time.time() - start_time

            # Read all speed meters and enable status
            speeds = []
            write_enables = []
            read_enables = []
            any_tx_active = False
            all_enable_off = True

            for i, sm in enumerate(speed_meters):
                speed_bps, speed_pps = sm.get_speed()
                speeds.append((speed_bps, speed_pps))

                # Check if any TX meter has throughput
                if i % 2 == 1 and speed_bps > 0:
                    any_tx_active = True

            # Read enable status for all cores
            for st in app_status_list:
                wr_en = st.capture_enable
                rd_en = st.read_enable
                write_enables.append(wr_en)
                read_enables.append(rd_en)
                if wr_en:
                    all_enable_off = False

            # Print sample
            line = f"{sample_count:>6} {elapsed:>8.1f}"
            for i in range(cores_cnt):
                rx_bps = speeds[i*2][0]
                tx_bps = speeds[i*2+1][0]
                wr_en = int(write_enables[i])
                rd_en = int(read_enables[i])
                line += f" | {rx_bps/10**9:>8.2f}G {tx_bps/10**9:>8.2f}G  {wr_en:^6}{rd_en:^6}"
            print(line)

            # Check stop condition: no TX throughput AND all enables are 0
            if not any_tx_active and all_enable_off:
                idle_count += 1
                if idle_count >= args.idle_threshold:
                    print(f"\nStop condition met: no TX throughput and all enables=0 for {args.idle_threshold} samples.")
                    break
            else:
                idle_count = 0

            # Clear meters for next sample
            for sm in speed_meters:
                sm.clear_data()

            time.sleep(args.sample_time)

    except KeyboardInterrupt:
        print("\n\nStopped by user")

    finally:
        # Restore terminal settings (line mode + echo)
        if old_term is not None:
            termios.tcsetattr(sys.stdin, termios.TCSADRAIN, old_term)

        # Disable capture on all cores
        print("\nDisabling capture...")
        for st in app_status_list:
            st.set_capture_enable(False)

        # Final reading
        print("\nFinal speed meter readings:")
        for i, sm in enumerate(speed_meters):
            speed_bps, speed_pps = sm.get_speed()
            core_id = i // 2
            direction = "RX" if i % 2 == 0 else "TX"
            print(f"Core {core_id} {direction}: {speed_bps/10**9:.2f} Gbps, {speed_pps:.0f} pps")

    return 0


if __name__ == "__main__":
    sys.exit(main())
