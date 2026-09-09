# cocotb_test.py: Component-level verification of MFB_COMPACTOR.
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# MFB_COMPACTOR removes empty regions between MFB frames and shifts occupied
# regions left so they are contiguous, while preserving frame order and the
# order of regions within a frame. Externally the observable contract is: an
# in-order, byte-exact MFB frame stream (the reference model is a plain
# in-order FIFO of frames), plus the structural invariant that no TX word may
# have an occupied region following an idle one (that would mean a gap was
# not removed).
#
# Stimulus notes:
#  - RX idle gaps (ItemRateLimiter) are used deliberately: they are what
#    forces frames to end up split across words with unoccupied regions in
#    the middle, which is exactly the case MFB_COMPACTOR needs to compact.
#    Without RX idles the input is already gapless and the DUT would be
#    exercised only on its pass-through path.
#  - TX backpressure is randomized independently of RX idles to exercise the
#    global-stall flow control together with a partially filled accumulator,
#    and the background _fwft_mode_checker continuously verifies RX_DST_RDY
#    against FWFT_MODE's ready equation regardless of which test is
#    running.
#  - META_WIDTH, USE_PIPE/FLUSH_TIMEOUT and FWFT_MODE are read from the
#    elaborated generics, not hardcoded, so the whole suite above also runs
#    unmodified under a GENERICS override (see ver_settings.py) to cover META
#    passthrough, the unregistered input path, the FLUSH_TIMEOUT=0 corner,
#    and the non-FWFT (plain wire) RX_DST_RDY.
#  - Frame lengths are only ever aligned to the item width (MFB's finest
#    granularity), never to a whole region: MFB must carry arbitrary
#    item-granular packet lengths, including under REGION_SIZE>1, so a region
#    can legitimately hold the tail of one frame and the head of the next.
#    The gap-checker below accounts for that ("shared" boundary regions).

import cocotb
import logging
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.mfb.drivers import MFBDriver
from cocotbext.ofm.mfb.monitors import MFBMonitor
from cocotbext.ofm.mfb.transaction import MfbTransaction, MfbTransactionWithMeta
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.ver.backpressure import BackpressureGenerator, BackpressureConfig
from cocotbext.ofm.ver.generators import random_packets
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard
from cocotbext.ofm.utils.throughput_probe import ThroughputProbe, ThroughputProbeMfbInterface
from random import randint


class GapInvariantError(Exception):
    pass


class FwftModeError(Exception):
    pass


class testbench():
    """Testbench for MFB_COMPACTOR: single MFB stream in, compacted MFB stream out."""

    def __init__(self, dut, debug=False):
        self.dut = dut

        mfb_params = {
            "regions"     : dut.REGIONS.value,
            "region_size" : dut.REGION_SIZE.value,
            "block_size"  : dut.BLOCK_SIZE.value,
            "item_width"  : dut.ITEM_WIDTH.value,
            "meta_width"  : dut.META_WIDTH.value,
        }

        self._regions = int(dut.REGIONS.value)
        self._meta_width = int(dut.META_WIDTH.value)
        self._fwft_mode = bool(int(dut.FWFT_MODE.value))

        self.mfb_stream_in = MFBDriver(dut, "RX", dut.CLK)
        # META_WIDTH=0 (the default) keeps the plain MfbTransaction; a non-zero
        # META_WIDTH (set via a GENERICS override) switches driver/model/monitor
        # to MfbTransactionWithMeta so the META passthrough path gets exercised.
        self.trans_type = MfbTransactionWithMeta if self._meta_width > 0 else MfbTransaction
        self.mfb_stream_out = MFBMonitor(dut, "TX", dut.CLK, mfb_params=mfb_params, trans_type=self.trans_type)

        self.mfb_backpressure = BitDriver(dut.TX_DST_RDY, dut.CLK)

        self.mfb_throughput_probe = ThroughputProbe(
            ThroughputProbeMfbInterface(self.mfb_stream_out), throughput_units="bits"
        )
        self.mfb_throughput_probe.add_log_interval(0, None)
        self.mfb_throughput_probe.set_log_period(10)

        self.mfb_expected_output = []

        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.mfb_stream_out, self.mfb_expected_output)

        if debug:
            self.mfb_stream_in.log.setLevel(logging.DEBUG)
            self.mfb_stream_out.log.setLevel(logging.DEBUG)

        cocotb.start_soon(self._tx_gap_checker())
        cocotb.start_soon(self._fwft_mode_checker())

    def model(self, mfb_transaction):
        """Reference model: in-order frame stream, no reordering, no drop, no split."""
        self.mfb_expected_output.append(mfb_transaction)

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 2)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)

    async def _tx_gap_checker(self):
        """Structural invariant: within one TX word, an occupied region may
        never follow an idle one. Tracks the in-frame carry from the TX
        stream itself (SOF/EOF sequence), independent of the DUT's internal
        state, so it is a black-box check of the compaction guarantee.
        """
        in_frame = False
        while True:
            await RisingEdge(self.dut.CLK)
            if self.dut.RESET.value == 1:
                in_frame = False
                continue
            if self.dut.TX_SRC_RDY.value != 1 or self.dut.TX_DST_RDY.value != 1:
                continue
            sof = int(self.dut.TX_SOF.value)
            eof = int(self.dut.TX_EOF.value)
            seen_idle = False
            for r in range(self._regions):
                s = (sof >> r) & 1
                e = (eof >> r) & 1
                occupied = in_frame or bool(s) or bool(e)
                if not occupied:
                    seen_idle = True
                elif seen_idle:
                    raise GapInvariantError(
                        f"MFB_COMPACTOR: occupied region {r} follows an idle region "
                        f"in the same TX word (sof={sof:#x}, eof={eof:#x})"
                    )
                # SOF and EOF together are ambiguous on their own: either a
                # frame that starts and ends within this one region (in_frame
                # was False entering it, stays False - closed), or a region
                # shared between an ending carried-over frame and a new one
                # that continues past it (in_frame was True entering it,
                # stays True - still open). Either way in_frame is unchanged;
                # only a lone SOF or a lone EOF actually flips it.
                if s and e:
                    pass
                elif s:
                    in_frame = True
                elif e:
                    in_frame = False

    async def _fwft_mode_checker(self):
        """Structural invariant: RX_DST_RDY must equal TX_DST_RDY (plain
        wire), or TX_DST_RDY or not TX_SRC_RDY when FWFT_MODE is set (data
        falls through) - checked every cycle, independent of whatever
        test/traffic pattern is running.
        """
        while True:
            await RisingEdge(self.dut.CLK)
            if self.dut.RESET.value == 1:
                continue
            rx_dst_rdy = int(self.dut.RX_DST_RDY.value)
            tx_dst_rdy = int(self.dut.TX_DST_RDY.value)
            tx_src_rdy = int(self.dut.TX_SRC_RDY.value)
            expected = tx_dst_rdy or (self._fwft_mode and not tx_src_rdy)
            if rx_dst_rdy != int(expected):
                raise FwftModeError(
                    f"RX_DST_RDY={rx_dst_rdy}, expected {int(expected)} "
                    f"(TX_DST_RDY={tx_dst_rdy}, TX_SRC_RDY={tx_src_rdy}, "
                    f"FWFT_MODE={self._fwft_mode})"
                )


def _item_bytes(tb):
    """MFB items are the finest addressable granularity (EOF_POS counts
    whole items); frame lengths must be a multiple of the item width for a
    byte-exact round trip through the driver/monitor.
    """
    return tb.mfb_stream_in._item_width // 8


async def _drive_and_model(tb, packets):
    for pkt in packets:
        tr = tb.trans_type()
        tr.data = pkt
        if hasattr(tr, "meta"):
            tr.meta = randint(0, 2**tb._meta_width - 1)
        tb.model(tr)
        tb.mfb_stream_in.append(tr)


async def _await_drain(tb, dut, exp_pkts):
    last_log = 0
    while tb.mfb_stream_out.frame_cnt < exp_pkts:
        if (tb.mfb_stream_out.frame_cnt // 1000) > last_log:
            last_log = tb.mfb_stream_out.frame_cnt // 1000
            cocotb.log.info("Transactions processed: %d/%d" % (tb.mfb_stream_out.frame_cnt, exp_pkts))
        await ClockCycles(dut.CLK, 100)
    cocotb.log.info("Transactions processed: %d/%d" % (tb.mfb_stream_out.frame_cnt, exp_pkts))


@cocotb.test()
async def run_test_basic(dut, pkt_count=5000, frame_size_min=8, frame_size_max=512):
    """Generic randomized test: gapless RX, randomized TX backpressure."""
    cocotb.start_soon(Clock(dut.CLK, 2, unit="ns").start())
    tb = testbench(dut, debug=False)
    await tb.reset()

    tb.mfb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    packets = list(random_packets(frame_size_min, frame_size_max, pkt_count, alignment=_item_bytes(tb)))
    await _drive_and_model(tb, packets)
    await _await_drain(tb, dut, pkt_count)

    tb.mfb_throughput_probe.log_max_throughput()
    tb.mfb_throughput_probe.log_average_throughput()
    raise tb.scoreboard.result


@cocotb.test()
async def run_test_rx_idles(dut, pkt_count=4000, frame_size_min=8, frame_size_max=512):
    """RX gaps between/within frames force real compaction work: without
    idles the input is already gapless. Also randomizes TX backpressure so a
    partially filled accumulator interacts with the global stall.
    """
    cocotb.start_soon(Clock(dut.CLK, 2, unit="ns").start())
    tb = testbench(dut, debug=False)
    await tb.reset()

    tb.mfb_stream_in.set_idle_generator(
        ItemRateLimiter(rate_percentage=0, random_idles=True, max_idles=int(dut.REGIONS.value), zero_idles_chance=40)
    )
    tb.mfb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    packets = list(random_packets(frame_size_min, frame_size_max, pkt_count, alignment=_item_bytes(tb)))
    await _drive_and_model(tb, packets)
    await _await_drain(tb, dut, pkt_count)
    raise tb.scoreboard.result


@cocotb.test()
async def run_test_min_frames(dut, pkt_count=3000):
    """Minimum-size (single item) frames back-to-back with RX idles: many
    small frames must compact into shared TX words (throughput/density
    check), while frame boundaries stay byte-exact.
    """
    cocotb.start_soon(Clock(dut.CLK, 2, unit="ns").start())
    tb = testbench(dut, debug=False)
    await tb.reset()

    tb.mfb_stream_in.set_idle_generator(
        ItemRateLimiter(rate_percentage=0, random_idles=True, max_idles=2, zero_idles_chance=60)
    )
    tb.mfb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 3, 0.5)))

    item_bytes = _item_bytes(tb)
    packets = list(random_packets(item_bytes, 4 * item_bytes, pkt_count, alignment=item_bytes))
    await _drive_and_model(tb, packets)
    await _await_drain(tb, dut, pkt_count)
    raise tb.scoreboard.result


@cocotb.test()
async def run_test_multiword_frames(dut, pkt_count=500):
    """Frames spanning 3+ words: middle words carry no SOF/EOF at all, only
    SRC_RDY, exercising the in-frame occupancy carry across whole words.
    """
    cocotb.start_soon(Clock(dut.CLK, 2, unit="ns").start())
    tb = testbench(dut, debug=False)
    await tb.reset()

    tb.mfb_stream_in.set_idle_generator(
        ItemRateLimiter(rate_percentage=0, random_idles=True, max_idles=3, zero_idles_chance=50)
    )
    tb.mfb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 4, 0.5)))

    word_bytes = int(dut.REGIONS.value) * int(dut.REGION_SIZE.value) * int(dut.BLOCK_SIZE.value) * int(dut.ITEM_WIDTH.value) // 8
    packets = list(random_packets(3 * word_bytes, 6 * word_bytes, pkt_count, alignment=_item_bytes(tb)))
    await _drive_and_model(tb, packets)
    await _await_drain(tb, dut, pkt_count)
    raise tb.scoreboard.result


@cocotb.test()
async def run_test_flush_drain(dut, burst_count=200, idle_gap_clocks=200):
    """Flush-timeout corner case: send a small burst that leaves a
    non-empty, non-full accumulator, then go fully idle on RX for much
    longer than FLUSH_TIMEOUT and confirm TX drains the leftovers on its
    own (no new RX data is needed to release them).
    """
    cocotb.start_soon(Clock(dut.CLK, 2, unit="ns").start())
    tb = testbench(dut, debug=False)
    await tb.reset()

    dut.TX_DST_RDY.value = 1

    item_bytes = _item_bytes(tb)
    total_pkts = 0
    for _ in range(burst_count):
        # Single-item frames guarantee each burst leaves a non-full,
        # non-empty accumulator remainder to be flushed.
        packets = list(random_packets(item_bytes, item_bytes, 3, alignment=item_bytes))
        await _drive_and_model(tb, packets)
        total_pkts += len(packets)
        await ClockCycles(dut.CLK, idle_gap_clocks)
        await _await_drain(tb, dut, total_pkts)

    raise tb.scoreboard.result


@cocotb.test()
async def run_test_reset_mid_stream(dut, pkt_count=800):
    """Reset asserted after a fully-drained burst, then a second burst
    resumes: guards against state carry-over in the occupancy carry and the
    accumulator/fill registers after an asynchronous restart.
    """
    cocotb.start_soon(Clock(dut.CLK, 2, unit="ns").start())
    tb = testbench(dut, debug=False)
    await tb.reset()

    tb.mfb_stream_in.set_idle_generator(
        ItemRateLimiter(rate_percentage=0, random_idles=True, max_idles=int(dut.REGIONS.value), zero_idles_chance=40)
    )
    tb.mfb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    item_bytes = _item_bytes(tb)
    pre_packets = list(random_packets(8, 256, pkt_count, alignment=item_bytes))
    await _drive_and_model(tb, pre_packets)
    await _await_drain(tb, dut, pkt_count)

    await tb.reset()

    post_packets = list(random_packets(8, 256, pkt_count, alignment=item_bytes))
    await _drive_and_model(tb, post_packets)
    await _await_drain(tb, dut, 2 * pkt_count)
    raise tb.scoreboard.result


class RegionCountError(Exception):
    pass


async def _count_tx_regions(dut, regions, counter):
    """Count the regions the compactor emits, tracking the in-frame carry from
    the TX stream itself. A region is occupied when a frame starts, ends, or
    simply continues through it.
    """
    in_frame = False
    while True:
        await RisingEdge(dut.CLK)
        if dut.RESET.value == 1:
            in_frame = False
            continue
        if dut.TX_SRC_RDY.value != 1 or dut.TX_DST_RDY.value != 1:
            continue
        sof = int(dut.TX_SOF.value)
        eof = int(dut.TX_EOF.value)
        for r in range(regions):
            s = (sof >> r) & 1
            e = (eof >> r) & 1
            if in_frame or s or e:
                counter["tx"] += 1
            if s and e:
                pass
            elif s:
                in_frame = True
            elif e:
                in_frame = False


async def _drive_raw_word(dut, sof, eof, eof_pos):
    """Drive one raw RX word and wait for it to be accepted. Bypasses MFBDriver
    on purpose: that driver only ever inserts idles before a transaction, so it
    cannot stall in the middle of a frame.
    """
    while True:
        dut.RX_DATA.value = 0
        dut.RX_SOF.value = sof
        dut.RX_EOF.value = eof
        dut.RX_SOF_POS.value = 0
        dut.RX_EOF_POS.value = eof_pos
        dut.RX_SRC_RDY.value = 1
        await RisingEdge(dut.CLK)
        if dut.RX_DST_RDY.value == 1:
            break
    dut.RX_SRC_RDY.value = 0


@cocotb.test()
async def run_test_flush_inside_frame(dut, stall_clocks=200):
    """Regression: a flush must not cut an unfinished frame.

    Leaves the accumulator holding the tail of a frame that has no EOF yet,
    then stalls RX for much longer than FLUSH_TIMEOUT. Padding a partial word
    would read as that frame continuing, so the compactor would emit regions
    it never received. Counting the occupied regions on TX catches exactly
    that, without depending on the payload encoding.
    """
    regions = int(dut.REGIONS.value)
    if regions < 2:
        # With REGIONS=1 the accumulator holds nothing, so it can never end
        # inside a frame and there is nothing to regress against.
        return

    eof_pos_max = int(dut.REGION_SIZE.value) * int(dut.BLOCK_SIZE.value) - 1

    cocotb.start_soon(Clock(dut.CLK, 2, unit="ns").start())
    dut.RX_SRC_RDY.value = 0
    dut.TX_DST_RDY.value = 1
    dut.RESET.value = 1
    await ClockCycles(dut.CLK, 4)
    dut.RESET.value = 0
    await RisingEdge(dut.CLK)

    counter = {"tx": 0}
    cocotb.start_soon(_count_tx_regions(dut, regions, counter))

    # A one-region frame, so the accumulator is left non-empty.
    await _drive_raw_word(dut, sof=1, eof=1, eof_pos=eof_pos_max)
    # A frame that starts here and is still open at the end of the word, so
    # every region is occupied and one of them stays in the accumulator.
    await _drive_raw_word(dut, sof=1, eof=0, eof_pos=0)
    rx_regions = 1 + regions

    # Nothing arrives for a long time: the flush timeout fires here.
    await ClockCycles(dut.CLK, stall_clocks)

    # The rest of the open frame, ending in region 0.
    await _drive_raw_word(dut, sof=0, eof=1, eof_pos=eof_pos_max)
    rx_regions += 1

    await ClockCycles(dut.CLK, stall_clocks)

    if counter["tx"] != rx_regions:
        raise RegionCountError(
            f"MFB_COMPACTOR emitted {counter['tx']} occupied regions, "
            f"received {rx_regions}: a flush cut an unfinished frame and its "
            f"padding read as the frame continuing"
        )
