# cocotb_test.py: cocotb test of the MFB_GENERATOR
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, RisingEdge
from cocotbext.ofm.mfb.monitors import MFBMonitor
from cocotbext.ofm.mfb.transaction import MfbTransactionWithMeta
from cocotbext.ofm.ver.backpressure import BackpressureConfig, apply_backpressure

HEADER_BITS = 384
ETHER_TYPE = 0x0008
IPV4_HEADER_BYTES = 20
UDP_HEADER_BYTES = 8
IP_VERSION_IHL = 0x45
IP_TTL = 0xFF
IP_PROTO_UDP = 0x11


def expected_packet(length, mac_dst, mac_src):
    """Frame the generator has to produce: the 384-bit header, then zeros up to the requested length (source IP masked to zero)"""
    l3len = (length - 14) & 0xFFFF
    l4len = (length - 34) & 0xFFFF
    ipv4 = (bytes([IP_VERSION_IHL, 0x00]) + l3len.to_bytes(2, "big") + bytes(4)
            + bytes([IP_TTL, IP_PROTO_UDP]) + bytes(2) + bytes(4) + bytes(4))
    udp = bytes(4) + l4len.to_bytes(2, "big") + bytes(2)
    assert len(ipv4) == IPV4_HEADER_BYTES and len(udp) == UDP_HEADER_BYTES
    header = (mac_dst.to_bytes(6, "little") + mac_src.to_bytes(6, "little") + ETHER_TYPE.to_bytes(2, "little")
              + ipv4 + udp + bytes(HEADER_BITS // 8 - 14 - IPV4_HEADER_BYTES - UDP_HEADER_BYTES))
    return header + bytes(length - len(header))


class Scoreboard:
    """Checks every received frame against the frame computed from its own metadata"""

    def __init__(self, mac_dst, mac_src, length_width):
        self.mac_dst = mac_dst
        self.mac_src = mac_src
        self.length_mask = 2**length_width - 1
        self.frames = 0
        self.errors = []

    def on_frame(self, tr):
        length = tr.meta & self.length_mask
        expected = expected_packet(length, self.mac_dst, self.mac_src)
        self.frames += 1
        if bytes(tr.data) != expected:
            first = next((i for i, (a, b) in enumerate(zip(tr.data, expected)) if a != b), min(len(tr.data), len(expected)))
            self.errors.append(f"frame {self.frames} of length {length} differs from byte {first}: "
                               f"got {bytes(tr.data)[first:first + 8].hex()}, expected {expected[first:first + 8].hex()}")

    def check(self):
        assert not self.errors, f"{len(self.errors)} bad frames, first: {self.errors[:3]}"


async def run_phase(dut, scoreboard, length, frames):
    """Generate frames of one length; the generator is stopped and drained first so that the metadata and the payload agree"""
    dut.CTRL_EN.value = 0
    await ClockCycles(dut.CLK, 200)
    dut.CTRL_LENGTH.value = length
    await ClockCycles(dut.CLK, 5)
    first = scoreboard.frames
    dut.CTRL_EN.value = 1
    for _ in range(100 * frames * (length // 32 + 1) + 1000):
        await RisingEdge(dut.CLK)
        if scoreboard.frames - first >= frames:
            return
    raise AssertionError(f"only {scoreboard.frames - first} of {frames} frames of {length} items arrived")


@cocotb.test()
async def test_headers(dut):
    """Header of every frame is the Ethernet, IPv4 and UDP header built from the control inputs, for every block width"""
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    regions = len(dut.TX_MFB_SOF)
    block_bits = len(dut.TX_MFB_DATA) // (regions * 2 ** (len(dut.TX_MFB_SOF_POS) // regions))
    length_width = len(dut.CTRL_LENGTH)
    cocotb.log.info(f"REGIONS={regions} block width={block_bits} bits LENGTH_WIDTH={length_width}")

    mac_dst = random.getrandbits(48)
    mac_src = random.getrandbits(48)
    scoreboard = Scoreboard(mac_dst, mac_src, length_width)
    monitor = MFBMonitor(dut, "TX_MFB", dut.CLK, trans_type=MfbTransactionWithMeta)
    monitor.add_callback(scoreboard.on_frame)

    dut.CTRL_EN.value = 0
    dut.CTRL_CHAN_INC.value = 0
    dut.CTRL_CHAN_VAL.value = 0
    dut.CTRL_MAC_DST.value = mac_dst
    dut.CTRL_MAC_SRC.value = mac_src
    dut.CTRL_PKT_CNT_CLR.value = 0
    dut.CTRL_SRC_IP_MASK.value = 0
    dut.CTRL_LENGTH.value = 64
    dut.TX_MFB_DST_RDY.value = 1
    dut.RST.value = 1
    await ClockCycles(dut.CLK, 10)
    dut.RST.value = 0
    await ClockCycles(dut.CLK, 10)

    cocotb.start_soon(apply_backpressure(dut.TX_MFB_DST_RDY, dut.CLK, BackpressureConfig(1, 6, 0.3)))

    # Lengths from the minimum that holds the header up to several words.
    max_length = min(1500, 2**length_width - 1)
    lengths = [64, 65, 100, 127, 128, 129, 255, 256, 511, max_length]
    random.shuffle(lengths)
    for length in lengths + [random.randint(64, max_length) for _ in range(10)]:
        await run_phase(dut, scoreboard, length, 20)

    dut.CTRL_EN.value = 0
    await ClockCycles(dut.CLK, 100)
    scoreboard.check()
    assert scoreboard.frames > 400
