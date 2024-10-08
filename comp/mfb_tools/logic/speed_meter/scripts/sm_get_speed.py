#!/usr/bin/env python3
# sm_get_speed.py: use the MFB Speed Meter to obtain
# TODO: Improve argument parsing and add more arguments (measurements, average, freq, offset(s), printing (+verbosity), ...)

import sys
import time
import nfb

dev = nfb.open()
comp = dev.comp_open("netcope,bus,mi", 0) # cesnet,ofm,gen_loop_switch

print_en = True
measurements = 10
if len(sys.argv) - 1 > 0:
    try:
        measurements = int(sys.argv[1])
    except TypeError:
        print("Invalid argument, defaulting to \"measurements=" + str(measurements) + "\"")

gls_freq = 200 * (10**6)

gls_offset = 0x5000
sm_gls_eth_rx_addr = gls_offset + 0x60
sm_gls_eth_tx_addr = gls_offset + 0x70


# Speed Meter reset
def sm_reset(sm_addr):
    comp.write32(sm_addr + 0xC, 0x1)


# Check if speed meter is done
def sm_done(sm_addr):
    done = 0
    check_cnt = 0
    while (done != 1 and check_cnt < 10):
        done = comp.read32(sm_addr + 0x4)
        # print("done("+str(check_cnt)+"): "+str(done))
        check_cnt += 1
        # print("check_cnt: "+str(check_cnt))
        time.sleep(0.02)
    return done == 1


def sm_measure(sm_addr, freq):
    if not sm_done(sm_addr):
        return None

    # Time in seconds for which the Speedmeter measured
    sm_run_time = comp.read32(sm_addr + 0x0) / freq
    # sm_run_time = 0x00ffffff/freq

    # read accumulated bits and convert to Gbps
    sm_gbs = comp.read32(sm_addr + 0x8) * 8 / (10**9)

    try:
        return round(sm_gbs / sm_run_time, 2)
    except ZeroDivisionError:
        return 0


def sm_average(data_set):
    try:
        return round(sum(data_set) / len(data_set), 2)
    except TypeError:
        return None


def main():
    speeds = []

    # print("-" * 30)
    for m in range(measurements):
        sm_reset(sm_gls_eth_tx_addr) # place rather into the sm_measure?

        try:
            sm_speed = sm_measure(sm_gls_eth_tx_addr, gls_freq)
        except TypeError:
            sm_speed = None
        speeds.append(sm_speed)

        if print_en:
            tmp_msg = "Measured speed #" + str(m + 1) + ": " + str(sm_speed) + " Gbps"
            print("-" * len(tmp_msg), tmp_msg, "-" * len(tmp_msg), sep="\n")

    if print_en:
        final_msg = "Average speed for " + str(measurements) + " measurements = " + str(sm_average(speeds)) + " Gbps"
        print(final_msg, "=" * len(final_msg), sep="\n")


if __name__ == "__main__":
    main()
