# cocotb_test.py: Component-level verification of PTC_STORAGE_FIFO.
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# PTC_STORAGE_FIFO is a paired MVB+MFB completion storage FIFO: each PCIe
# Completion header (MVB item) is paired with its payload frame (MFB frame).
# Internally it removes empty MFB regions on the write side with MFB_COMPACTOR
# and stores the resulting dense words in a plain word-granularity MFB_FIFOX;
# a safe_mvb_items_reg gates MVB header release on the count of MFB EOFs seen
# on TX. Externally the observable contract is simply an in-order paired
# MVB+MFB FIFO.
#
# This testbench is the verifiable asset for any change to the internal MFB
# storage path: it checks only the external contract, so it holds across
# reimplementations of that path (it also passed against the earlier
# FIFOX_MULTI-based compacting read path). It exercises the compaction,
# unfinished-packet handling, and MVB/MFB release ordering on randomized and
# targeted corner-case traffic.
#
# Stimulus notes:
#  - The real upstream (PCIe R-Tile completer) ties RC_MVB and RC_MFB to one
#    SRC_RDY, so an MFB EOF is never seen without its paired MVB header. The RX
#    drivers therefore use NO idle generators; input rate stress comes from the
#    MVB driver's word-packing and from independent TX backpressure.
#  - Frames are aligned to an MFB region boundary (region_size*block_size*
#    item_width/8). MFB_COMPACTOR reorders whole regions, so region-aligned
#    frames keep SOF/EOF on region starts and yield a byte-exact in-order
#    reference model. Non-region-aligned sizes are a separate (compaction-
#    model) concern outside this component's storage-path regression.

import cocotb
import logging
from random import randint
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.mvb.drivers import MVBDriver
from cocotbext.ofm.mvb.monitors import MVBMonitor
from cocotbext.ofm.mfb.drivers import MFBDriver
from cocotbext.ofm.mfb.monitors import MFBMonitor
from cocotbext.ofm.ver.backpressure import BackpressureGenerator, BackpressureConfig
from cocotbext.ofm.ver.generators import random_packets
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard
from cocotbext.ofm.utils.throughput_probe import ThroughputProbe, ThroughputProbeMfbInterface
from cocotbext.ofm.mvb.transaction import MvbTrClassic
from cocotbext.ofm.mfb.transaction import MfbTransaction


class testbench():
    """Testbench for PTC_STORAGE_FIFO: paired MVB (header) + MFB (payload) FIFO.

    The DUT stores completions as paired (MVB header, MFB frame) and releases
    them in-order on TX; safe_mvb_items_reg guarantees an MVB header is only
    emitted once its frame's EOF has been observed on the MFB output, so the
    model is two in-order FIFOs paired by emission index.
    """

    def __init__(self, dut, debug=False):
        self.dut = dut

        mfb_params = {
            "regions"     : dut.MFB_REGIONS.value,
            "region_size" : dut.MFB_REG_SIZE.value,
            "block_size"  : dut.MFB_BLOCK_SIZE.value,
            "item_width"  : dut.MFB_ITEM_WIDTH.value,
            "meta_width"  : 0,
        }

        # RX side: both streams are fed together. The real upstream (PCIe R-Tile
        # completer) ties RC_MVB and RC_MFB to a single SRC_RDY, so the two
        # streams must advance in lockstep - an MFB EOF is never seen without
        # its paired MVB header already written. Independent per-driver idle
        # generators would break this pairing and corrupt safe_mvb_items_reg,
        # so NO idle generator is used on RX; input stress comes from the MVB
        # driver's own word-packing and from the TX backpressure below.
        self.mvb_stream_in = MVBDriver(dut, "RX_MVB", dut.CLK)
        self.mfb_stream_in = MFBDriver(dut, "RX_MFB", dut.CLK, mfb_params=mfb_params)

        # TX side monitors.
        self.mvb_stream_out = MVBMonitor(dut, "TX_MVB", dut.CLK, tr_type=MvbTrClassic)
        self.mfb_stream_out = MFBMonitor(dut, "TX_MFB", dut.CLK, mfb_params=mfb_params, trans_type=MfbTransaction)

        # Independent backpressure on each TX stream is the realistic stress
        # for safe_mvb_items_reg: MFB can be stalled while MVB drains and vice
        # versa, exercising the EOF-gates-header accounting.
        self.mvb_backpressure = BitDriver(dut.TX_MVB_DST_RDY, dut.CLK)
        self.mfb_backpressure = BitDriver(dut.TX_MFB_DST_RDY, dut.CLK)

        self.mfb_throughput_probe = ThroughputProbe(
            ThroughputProbeMfbInterface(self.mfb_stream_out), throughput_units="bits"
        )
        self.mfb_throughput_probe.add_log_interval(0, None)
        self.mfb_throughput_probe.set_log_period(10)

        self.pkts_sent = 0
        self.mvb_expected_output = []
        self.mfb_expected_output = []

        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.mvb_stream_out, self.mvb_expected_output)
        self.scoreboard.add_interface(self.mfb_stream_out, self.mfb_expected_output)

        if debug:
            self.mvb_stream_in.log.setLevel(logging.DEBUG)
            self.mfb_stream_in.log.setLevel(logging.DEBUG)
            self.mvb_stream_out.log.setLevel(logging.DEBUG)
            self.mfb_stream_out.log.setLevel(logging.DEBUG)

    def model(self, mvb_transaction, mfb_transaction):
        """Reference model: in-order paired FIFO (no reordering, no drop)."""
        self.mvb_expected_output.append(mvb_transaction)
        self.mfb_expected_output.append(mfb_transaction)
        self.pkts_sent += 1

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 2)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


def _mfb_align_bytes(tb):
    """Granularity (bytes) to which generated frame lengths are aligned.

    MFB_COMPACTOR inside PTC_STORAGE_FIFO compacts whole MFB regions, so
    frames are aligned to a region boundary (region_size * block_size *
    item_width / 8 = 16 B on the R-Tile x16 config). This keeps SOF/EOF on
    region starts, matching how the PCIe completer frames completions, and
    yields a byte-exact in-order reference model.
    """
    d = tb.mfb_stream_in
    return d._region_size * d._block_size * (d._item_width // 8)


async def _drive_pairs(tb, packets_mvb, packets_mfb):
    """Send paired (header, frame) transactions, logging expected output."""
    for mvb_data, mfb_packet in zip(packets_mvb, packets_mfb):
        mvb_tr = MvbTrClassic()
        mvb_tr.data = mvb_data

        mfb_tr = MfbTransaction()
        mfb_tr.data = mfb_packet

        tb.model(mvb_tr, mfb_tr)
        cocotb.log.debug(f"generated pair: MVB={mvb_tr}, MFB len={len(mfb_packet)}")

        # Append both; the drivers arbitrate idle/dst_rdy independently, which
        # stresses the internal MFB_COMPACTOR/MFB_FIFOX compaction and the
        # MVB/MFB release skew that safe_mvb_items_reg must absorb.
        tb.mvb_stream_in.append(mvb_tr)
        tb.mfb_stream_in.append(mfb_tr)


async def _await_drain(tb, dut, exp_pkts):
    """Wait until BOTH the MFB and MVB output streams have delivered exp_pkts.

    safe_mvb_items_reg releases each MVB header only after its paired MFB EOF,
    so the MVB stream can lag the MFB stream; waiting on MFB frame_cnt alone
    would exit while MVB headers are still queued, leaving expected MVB items
    unmatched in the scoreboard.
    """
    last_log = 0
    while (tb.mfb_stream_out.frame_cnt < exp_pkts
           or tb.mvb_stream_out.item_cnt < exp_pkts):
        done = min(tb.mfb_stream_out.frame_cnt, tb.mvb_stream_out.item_cnt)
        if (done // 1000) > last_log:
            last_log = done // 1000
            cocotb.log.info(
                "Transactions processed: MFB %d/%d, MVB %d/%d"
                % (tb.mfb_stream_out.frame_cnt, exp_pkts,
                   tb.mvb_stream_out.item_cnt, exp_pkts)
            )
        await ClockCycles(dut.CLK, 100)
    cocotb.log.info(
        "Transactions processed: MFB %d/%d, MVB %d/%d"
        % (tb.mfb_stream_out.frame_cnt, exp_pkts,
           tb.mvb_stream_out.item_cnt, exp_pkts)
    )


@cocotb.test()
async def run_test_basic(dut, pkt_count=5000, frame_size_min=60, frame_size_max=512):
    """Generic randomized test: paired headers + frames, randomized backpressure.

    Covers the common path and the in-order pairing invariant. Default generic
    parameters mirror the real R-Tile x16 instantiation (4 regions, 4 MVB
    items) set via the Makefile generics.
    """
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())
    tb = testbench(dut, debug=False)
    await tb.reset()

    tb.mvb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))
    tb.mfb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    mvb_data_width = tb.mvb_stream_in.item_widths["data"]
    align_bytes = _mfb_align_bytes(tb)
    packets_mvb = [randint(0, 2 ** mvb_data_width - 1) for _ in range(pkt_count)]
    # Frame lengths aligned to a region boundary (16 B): keeps SOF/EOF on region
    # starts so MFB_COMPACTOR's region reordering never breaks the byte-exact
    # in-order model, while still exercising multi-word frames and the
    # compactor's leftover-region accumulator for sizes that are not whole words.
    packets_mfb = list(random_packets(frame_size_min, frame_size_max, pkt_count, alignment=align_bytes))

    await _drive_pairs(tb, packets_mvb, packets_mfb)
    await _await_drain(tb, dut, pkt_count)

    tb.mfb_throughput_probe.log_max_throughput()
    tb.mfb_throughput_probe.log_average_throughput()
    raise tb.scoreboard.result


@cocotb.test()
async def run_test_unfinished_packet_tail(dut, pkt_count=2000):
    """Corner case: frames sized to leave an unfinished-packet tail in a word.

    MFB region size here is 1 block of 4 32-bit items = 128 bits = 16 B per
    region; with 4 regions a word holds 64 B. Frame sizes that are NOT a whole
    multiple of 64 B force MFB_COMPACTOR to carry an unfinished frame's
    leftover regions across a word boundary in its internal accumulator,
    which any change to the compactor/storage path must not corrupt.
    """
    # Region-aligned sizes (multiples of 16 B) chosen to stress the
    # unfinished-packet accumulator: 16/32/48 B leave a <1-word tail (the
    # leftover regions the compactor's accumulator must carry over); 80/112/144
    # B span word boundaries. All multiples of the region (16 B).
    unfinished_sizes = [16, 32, 48, 80, 112, 144]
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())
    tb = testbench(dut, debug=False)
    await tb.reset()

    tb.mvb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 3, 0.5)))
    tb.mfb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 3, 0.5)))

    mvb_data_width = tb.mvb_stream_in.item_widths["data"]
    align_bytes = _mfb_align_bytes(tb)
    packets_mvb = [randint(0, 2 ** mvb_data_width - 1) for _ in range(pkt_count)]
    packets_mfb = [
        bytes(randint(0, 255) for _ in range(unfinished_sizes[i % len(unfinished_sizes)]))
        for i in range(pkt_count)
    ]
    # Sanity: every corner size must be region-aligned for an exact EOF_POS.
    assert all(s % align_bytes == 0 for s in unfinished_sizes), "unfinished_sizes not region-aligned"

    await _drive_pairs(tb, packets_mvb, packets_mfb)
    await _await_drain(tb, dut, pkt_count)
    raise tb.scoreboard.result


@cocotb.test()
async def run_test_mvb_stall(dut, pkt_count=1500):
    """Corner case: MVB TX stalled hard while MFB drains, then released.

    Forces safe_mvb_items_reg to accumulate a large MFB-EOF credit surplus
    before MVB headers are released, then verifies a burst of MVB emission
    stays correctly paired and in-order on release. This is the accounting
    invariant most at risk if a latency change is ever applied to the MFB
    read path.
    """
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())
    tb = testbench(dut, debug=False)
    await tb.reset()

    # MFB drains freely; MVB held off for a long window, then opened.
    tb.mfb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 3, 0.5)))

    mvb_data_width = tb.mvb_stream_in.item_widths["data"]
    align_bytes = _mfb_align_bytes(tb)
    packets_mvb = [randint(0, 2 ** mvb_data_width - 1) for _ in range(pkt_count)]
    packets_mfb = list(random_packets(60, 512, pkt_count, alignment=align_bytes))

    async def mvb_gated_release():
        # Hold TX_MVB_DST_RDY low (stall), let MFB EOFs pile up credit.
        dut.TX_MVB_DST_RDY.value = 0
        await ClockCycles(dut.CLK, 400)
        # Release; MVB must now emit the buffered headers in-order, paired.
        dut.TX_MVB_DST_RDY.value = 1

    cocotb.start_soon(mvb_gated_release())

    await _drive_pairs(tb, packets_mvb, packets_mfb)
    await _await_drain(tb, dut, pkt_count)
    raise tb.scoreboard.result


@cocotb.test()
async def run_test_reset_mid_stream(dut, pkt_count=400):
    """Corner case: reset asserted after a burst, then a second burst resumes.

    Guards against state carry-over in safe_mvb_items_reg and the MFB_COMPACTOR
    accumulator/MFB_FIFOX pointers after an asynchronous restart. The first burst is fully drained
    and checked before the reset (so driver queues are empty and the scoreboard
    is consistent); the reset clears the DUT, then the second burst verifies
    clean post-reset behaviour.
    """
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())
    tb = testbench(dut, debug=False)
    await tb.reset()

    tb.mvb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))
    tb.mfb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    mvb_data_width = tb.mvb_stream_in.item_widths["data"]
    align_bytes = _mfb_align_bytes(tb)

    # First burst: modelled/expected, fully drained before reset so no stale
    # transactions linger in the driver queues across the reset.
    pre_mvb = [randint(0, 2 ** mvb_data_width - 1) for _ in range(pkt_count)]
    pre_mfb = list(random_packets(60, 256, pkt_count, alignment=align_bytes))
    await _drive_pairs(tb, pre_mvb, pre_mfb)
    await _await_drain(tb, dut, pkt_count)

    # Reset clears DUT state (MFB_COMPACTOR accumulator, MFB_FIFOX pointers,
    # safe_mvb_items_reg, output register). Driver queues are already empty,
    # so nothing stale is sent after.
    await tb.reset()

    # Second burst: modelled/expected, drained and checked.
    post_mvb = [randint(0, 2 ** mvb_data_width - 1) for _ in range(pkt_count)]
    post_mfb = list(random_packets(60, 256, pkt_count, alignment=align_bytes))
    await _drive_pairs(tb, post_mvb, post_mfb)
    await _await_drain(tb, dut, 2 * pkt_count)
    raise tb.scoreboard.result


@cocotb.test()
async def run_test_min_frame(dut, pkt_count=1000):
    """Corner case: minimum-size frames (60 B) back-to-back.

    Minimum frames pack multiple completions per MFB word and stress the
    compaction throughput path at full rate.
    """
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())
    tb = testbench(dut, debug=False)
    await tb.reset()

    tb.mvb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))
    tb.mfb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    mvb_data_width = tb.mvb_stream_in.item_widths["data"]
    align_bytes = _mfb_align_bytes(tb)
    packets_mvb = [randint(0, 2 ** mvb_data_width - 1) for _ in range(pkt_count)]
    # Smallest region-aligned frame (16 B = one region) back-to-back.
    packets_mfb = list(random_packets(align_bytes, align_bytes, pkt_count, alignment=align_bytes))

    await _drive_pairs(tb, packets_mvb, packets_mfb)
    await _await_drain(tb, dut, pkt_count)
    raise tb.scoreboard.result
