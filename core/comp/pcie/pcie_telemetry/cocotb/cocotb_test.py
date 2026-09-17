# cocotb_test.py:
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import random

import cocotb
from cocotb.triggers import RisingEdge, Timer, ClockCycles
from cocotb.clock import Clock
from cocotbext.ofm.mi.drivers import MIRequestDriver

# Register map, byte offsets
REG_MAGIC = 0x0000
REG_VERSION = 0x0004
REG_TOPOLOGY = 0x0008
REG_LAYOUT = 0x000C
REG_CFG_PCIE = 0x0010
REG_CFG_DMA = 0x0014
REG_CFG_WIDTH = 0x0030
REG_CFG_WIDTH_DMA = 0x003C
REG_CFG_HIST = 0x0034
REG_CFG_CAPACITY = 0x0038
REG_DRAIN = 0x0018
REG_CNT_BASE = 0x001C
REG_COMMAND = 0x0020
REG_STATUS = 0x0024
REG_READ_SEL = 0x0028
REG_PCIE_STATUS = 0x0040
REG_PCIE_TAGS = 0x0080
REG_PCIE_STFIFO = 0x00C0

CMD_SNAPSHOT = 1 << 0
CMD_CLEAR = 1 << 1
CMD_CLEAR_FLAGS = 1 << 2

MAGIC = 0x50544C4D


class Probe:
    """Software model of one telemetry probe."""

    def __init__(self, buses, regions, brakes, items):
        self.buses = buses
        self.regions = regions
        self.brakes = brakes
        self.items = items
        self.bus_channels = 6 + regions
        self.channels = 1 + buses * self.bus_channels + brakes
        self.cnt = [0] * self.channels
        self.frame_open = [0] * buses

    def sample(self, sof, eof, eof_pos, src_rdy, dst_rdy, brake, mvb):
        """Counts one clock cycle of the observed signals."""
        self.cnt[0] += 1

        for b in range(self.buses):
            base = 1 + b * self.bus_channels
            move = src_rdy[b] and dst_rdy[b]
            hold = src_rdy[b] and not dst_rdy[b]

            frm_open = self.frame_open[b]
            region_vld = []
            for r in range(self.regions):
                region_vld.append(frm_open or sof[b][r])
                frm_open = (frm_open or sof[b][r]) and not eof[b][r]

            if move:
                self.cnt[base + 0] += 1
                self.cnt[base + 2] += sum(sof[b])
                for r in range(self.regions):
                    if region_vld[r]:
                        # A region that ends a frame carries the items up to
                        # EOF_POS. Any other region of an open frame carries
                        # all of its items.
                        if eof[b][r]:
                            self.cnt[base + 5] += eof_pos[b][r] + 1
                        else:
                            self.cnt[base + 5] += self.items[b]
                        self.cnt[base + 6 + r] += 1
                self.frame_open[b] = frm_open
            if hold:
                self.cnt[base + 1] += 1

            mvb_vld, mvb_src, mvb_dst = mvb
            if mvb_src[b] and mvb_dst[b]:
                self.cnt[base + 3] += sum(mvb_vld[b])
            if mvb_src[b] and not mvb_dst[b]:
                self.cnt[base + 4] += 1

        for k in range(self.brakes):
            if brake[k]:
                self.cnt[1 + self.buses * self.bus_channels + k] += 1


class Stimulus:
    """Random MFB traffic for one probe, with a matching software model."""

    def __init__(self, buses, regions, brakes, seed, items, has_mvb=False):
        self.buses = buses
        self.regions = regions
        self.brakes = brakes
        self.items = items
        self.has_mvb = has_mvb
        self.rnd = random.Random(seed)
        self.model = Probe(buses, regions, brakes, items)
        self.open_frame = [False] * buses
        self.idle = False

    def next_value(self):
        """Returns one cycle of stimulus for the observed buses.

        The tuple is ``(sof, eof, eof_pos, src_rdy, dst_rdy, brake, mvb)``.
        Its ``brake`` item holds the value of the BRAKE port in that cycle.
        """
        sof = [[0] * self.regions for _ in range(self.buses)]
        eof = [[0] * self.regions for _ in range(self.buses)]
        eof_pos = [[0] * self.regions for _ in range(self.buses)]
        src_rdy = [0] * self.buses
        dst_rdy = [0] * self.buses
        brake = [0] * self.brakes
        mvb_vld = [[0] * self.regions for _ in range(self.buses)]
        mvb_src = [0] * self.buses
        mvb_dst = [0] * self.buses
        mvb = (mvb_vld, mvb_src, mvb_dst)

        if self.idle:
            return sof, eof, eof_pos, src_rdy, dst_rdy, brake, mvb

        # The MVB has a handshake of its own. It is not tied to the MFB one.
        if self.has_mvb:
            for b in range(self.buses):
                mvb_src[b] = 1 if self.rnd.random() < 0.6 else 0
                mvb_dst[b] = 1 if self.rnd.random() < 0.7 else 0
                for r in range(self.regions):
                    mvb_vld[b][r] = 1 if self.rnd.random() < 0.5 else 0

        for b in range(self.buses):
            src_rdy[b] = 1 if self.rnd.random() < 0.7 else 0
            dst_rdy[b] = 1 if self.rnd.random() < 0.8 else 0
            if not (src_rdy[b] and dst_rdy[b]):
                continue
            # Keep the SOF/EOF sequence legal: a frame must be opened before it
            # can be closed and only one frame may be open at a time.
            for r in range(self.regions):
                if self.open_frame[b]:
                    if self.rnd.random() < 0.5:
                        eof[b][r] = 1
                        self.open_frame[b] = False
                elif self.rnd.random() < 0.5:
                    sof[b][r] = 1
                    self.open_frame[b] = True
                    if self.rnd.random() < 0.3:
                        eof[b][r] = 1
                        self.open_frame[b] = False
                if eof[b][r]:
                    eof_pos[b][r] = self.rnd.randrange(self.items[b])

        for k in range(self.brakes):
            brake[k] = 1 if self.rnd.random() < 0.2 else 0

        return sof, eof, eof_pos, src_rdy, dst_rdy, brake, mvb


def pack_bits(per_bus):
    """Packs a list of per-bus region lists into one integer, bus 0 lowest."""
    value = 0
    pos = 0
    for bus in per_bus:
        for bit in bus:
            value |= bit << pos
            pos += 1
    return value


def pack_fields(per_bus, width):
    """Packs per-bus region fields of the given width, bus 0 lowest."""
    value = 0
    pos = 0
    for bus in per_bus:
        for field in bus:
            value |= field << pos
            pos += width
    return value


def pack_flags(flags):
    value = 0
    for i, bit in enumerate(flags):
        value |= bit << i
    return value


class VectorClock:
    """Drives all bits of a clock vector and calls a callback after every edge.

    A packed VHDL vector cannot be used in an edge trigger, so everything driven
    synchronously to this clock is driven from the hook.
    """

    def __init__(self, sig, period_ns, width):
        self.sig = sig
        self.period_ns = period_ns
        self.width = width
        self.hook = None

    async def run(self):
        half = Timer(self.period_ns / 2, unit="ns")
        high = (1 << self.width) - 1
        while True:
            self.sig.value = high
            await half
            if self.hook is not None:
                self.hook()
            self.sig.value = 0
            await half


class TB:
    def __init__(self, dut):
        self.dut = dut
        self.mi = MIRequestDriver(dut, "MI", dut.MI_CLK)

    async def start(self):
        cocotb.start_soon(Clock(self.dut.MI_CLK, 10, unit="ns").start())
        self.endpoints = len(self.dut.PCIE_CLK)
        self.pcie_clk = VectorClock(self.dut.PCIE_CLK, 2, self.endpoints)
        cocotb.start_soon(self.pcie_clk.run())
        cocotb.start_soon(Clock(self.dut.DMA_CLK, 4, unit="ns").start())

    async def reset(self):
        self.dut.MI_RESET.value = 1
        self.dut.PCIE_RESET.value = (1 << self.endpoints) - 1
        self.dut.DMA_RESET.value = 1
        await Timer(200, unit="ns")
        self.dut.MI_RESET.value = 0
        self.dut.PCIE_RESET.value = 0
        self.dut.DMA_RESET.value = 0
        await ClockCycles(self.dut.MI_CLK, 5)

    async def read_config(self):
        magic = await self.mi.read32(REG_MAGIC)
        assert magic == MAGIC, f"Bad magic 0x{magic:08X}"

        topo = await self.mi.read32(REG_TOPOLOGY)
        layout = await self.mi.read32(REG_LAYOUT)
        cfg_pcie = await self.mi.read32(REG_CFG_PCIE)
        cfg_dma = await self.mi.read32(REG_CFG_DMA)

        self.pcie_endpoints = topo & 0xFF
        self.dma_ports = (topo >> 8) & 0xFF
        self.streams = (topo >> 16) & 0xFF
        self.entries = layout & 0xFFFF
        self.cnt_width = (layout >> 16) & 0xFF
        self.ep_channels = (layout >> 24) & 0xFF
        self.pcie_channels = cfg_pcie & 0xFF
        self.pcie_buses = (cfg_pcie >> 8) & 0xFF
        self.pcie_regions = (cfg_pcie >> 16) & 0xFF
        self.pcie_brakes = (cfg_pcie >> 24) & 0xFF
        self.dma_channels = cfg_dma & 0xFF
        self.dma_buses = (cfg_dma >> 8) & 0xFF
        self.dma_regions = (cfg_dma >> 16) & 0xFF
        self.dma_brakes = (cfg_dma >> 24) & 0xFF
        drain = await self.mi.read32(REG_DRAIN)
        self.drain_period = drain & 0xFFFF
        self.item_bytes = (drain >> 16) & 0xFF
        self.cnt_base = await self.mi.read32(REG_CNT_BASE)

        # Items in one region of every observed bus, in the order in which the
        # probes observe them. The PCIe probe takes RQ and then RC. The DMA
        # probe takes UP and then DOWN.
        width = await self.mi.read32(REG_CFG_WIDTH)
        self.pcie_items = [(width & 0xFFFF) // self.item_bytes,
                           ((width >> 16) & 0xFFFF) // self.item_bytes]
        width = await self.mi.read32(REG_CFG_WIDTH_DMA)
        dma_items = [(width & 0xFFFF) // self.item_bytes,
                     ((width >> 16) & 0xFFFF) // self.item_bytes]
        self.dma_items = [dma_items[b % 2] for b in range(self.dma_buses)]
        self.pos_width = max(self.pcie_items + self.dma_items).bit_length() - 1

        cfg_hist = await self.mi.read32(REG_CFG_HIST)
        cfg_cap = await self.mi.read32(REG_CFG_CAPACITY)
        self.hist_bands = cfg_hist & 0xFF
        self.pcie_hists = (cfg_hist >> 8) & 0xFF
        self.dma_hists = (cfg_hist >> 16) & 0xFF
        self.tag_capacity = cfg_cap & 0xFFFF
        self.stfifo_capacity = (cfg_cap >> 16) & 0xFFFF

        # The histogram bands are stored after the BRAKE channels. Only the
        # BRAKE channels are driven by the stimulus and modelled.
        self.pcie_driven_brakes = self.pcie_brakes - self.pcie_hists * self.hist_bands
        self.dma_driven_brakes = self.dma_brakes - self.dma_hists * self.hist_bands
        assert self.pcie_driven_brakes >= 0 and self.dma_driven_brakes >= 0

        assert self.pcie_endpoints == self.endpoints
        assert self.streams == 2 * self.pcie_endpoints
        assert self.ep_channels == self.pcie_channels + self.dma_channels

        cocotb.log.info(
            f"endpoints={self.pcie_endpoints} dma_ports={self.dma_ports} "
            f"pcie_channels={self.pcie_channels} dma_channels={self.dma_channels} "
            f"entries={self.entries} cnt_width={self.cnt_width} "
            f"drain_period={self.drain_period}"
        )

    def stream_base(self, ep, dma_side):
        base = ep * self.ep_channels
        return base + self.pcie_channels if dma_side else base

    async def read_counter(self, index):
        lo = await self.mi.read32(self.cnt_base + 8 * index)
        hi = await self.mi.read32(self.cnt_base + 8 * index + 4)
        return lo | (hi << 32)

    async def snapshot(self):
        await self.mi.write(REG_COMMAND, CMD_SNAPSHOT.to_bytes(4, "little"))
        for _ in range(1000):
            if (await self.mi.read32(REG_STATUS)) & 1 == 0:
                return
        raise AssertionError("Snapshot did not finish")

    async def clear(self):
        await self.mi.write(REG_COMMAND, CMD_CLEAR.to_bytes(4, "little"))
        for _ in range(1000):
            if (await self.mi.read32(REG_STATUS)) & 1 == 0:
                return
        raise AssertionError("Clear did not finish")


class DomainDriver:
    """Applies one cycle of stimulus to all endpoints of one clock domain."""

    def __init__(self, sof_sig, eof_sig, eof_pos_sig, pos_width, src_sig, dst_sig,
                 brake_sig, stims, cycles, mvb_sigs=None):
        self.sof_sig = sof_sig
        self.eof_sig = eof_sig
        self.eof_pos_sig = eof_pos_sig
        self.pos_width = pos_width
        self.src_sig = src_sig
        self.dst_sig = dst_sig
        self.brake_sig = brake_sig
        self.mvb_sigs = mvb_sigs
        self.stims = stims
        self.left = cycles
        self.done = False

    def step(self):
        if self.left == 0:
            if not self.done:
                self.idle()
                self.done = True
            return
        self.left -= 1
        for ep, stim in enumerate(self.stims):
            sof, eof, eof_pos, src_rdy, dst_rdy, brake, mvb = stim.next_value()
            stim.model.sample(sof, eof, eof_pos, src_rdy, dst_rdy, brake, mvb)
            self.sof_sig[ep].value = pack_bits(sof)
            self.eof_sig[ep].value = pack_bits(eof)
            self.eof_pos_sig[ep].value = pack_fields(eof_pos, self.pos_width)
            self.src_sig[ep].value = pack_flags(src_rdy)
            self.dst_sig[ep].value = pack_flags(dst_rdy)
            if self.brake_sig is not None:
                self.brake_sig[ep].value = pack_flags(brake)
            if self.mvb_sigs is not None:
                vld_sig, src_sig, dst_sig = self.mvb_sigs
                mvb_vld, mvb_src, mvb_dst = mvb
                vld_sig[ep].value = pack_bits(mvb_vld)
                src_sig[ep].value = pack_flags(mvb_src)
                dst_sig[ep].value = pack_flags(mvb_dst)

    def idle(self):
        for ep in range(len(self.stims)):
            self.sof_sig[ep].value = 0
            self.eof_sig[ep].value = 0
            self.eof_pos_sig[ep].value = 0
            self.src_sig[ep].value = 0
            self.dst_sig[ep].value = 0
            if self.brake_sig is not None:
                self.brake_sig[ep].value = 0
            if self.mvb_sigs is not None:
                for sig in self.mvb_sigs:
                    sig[ep].value = 0


async def run_domain(clk, driver, cycles):
    """Drives a scalar clock domain."""
    for _ in range(cycles + 1):
        await RisingEdge(clk)
        driver.step()


@cocotb.test()
async def run_test(dut):
    tb = TB(dut)
    await tb.start()

    for ep in range(tb.endpoints):
        dut.PCIE_MFB_SOF[ep].value = 0
        dut.PCIE_MFB_EOF[ep].value = 0
        dut.PCIE_MFB_EOF_POS[ep].value = 0
        dut.PCIE_MFB_SRC_RDY[ep].value = 0
        dut.PCIE_MFB_DST_RDY[ep].value = 0
        dut.PCIE_PTC_BRAKE[ep].value = 0
        dut.PCIE_STFIFO_FREE[ep].value = 1000
        dut.PCIE_MPS[ep].value = 1
        dut.PCIE_MRRS[ep].value = 2
        dut.PCIE_TAG_FREE[ep].value = 256
        dut.DMA_MFB_SOF[ep].value = 0
        dut.DMA_MFB_EOF[ep].value = 0
        dut.DMA_MFB_EOF_POS[ep].value = 0
        dut.DMA_MFB_SRC_RDY[ep].value = 0
        dut.DMA_MFB_DST_RDY[ep].value = 0
    dut.PCIE_EXT_TAG_EN.value = (1 << tb.endpoints) - 1
    dut.PCIE_10B_TAG_REQ_EN.value = 0
    dut.PCIE_RCB_SIZE.value = (1 << tb.endpoints) - 1
    dut.PCIE_LINK_UP.value = (1 << tb.endpoints) - 1

    await tb.reset()
    await tb.read_config()

    cocotb.log.info("PHASE 1: random traffic")

    pcie_stims = [Stimulus(tb.pcie_buses, tb.pcie_regions, tb.pcie_driven_brakes,
                           100 + ep, tb.pcie_items)
                  for ep in range(tb.endpoints)]
    dma_stims = [Stimulus(tb.dma_buses, tb.dma_regions, tb.dma_driven_brakes,
                          200 + ep, tb.dma_items, has_mvb=True)
                 for ep in range(tb.endpoints)]

    traffic_cycles = 6 * tb.drain_period

    pcie_driver = DomainDriver(
        dut.PCIE_MFB_SOF, dut.PCIE_MFB_EOF, dut.PCIE_MFB_EOF_POS, tb.pos_width,
        dut.PCIE_MFB_SRC_RDY, dut.PCIE_MFB_DST_RDY, dut.PCIE_PTC_BRAKE,
        pcie_stims, traffic_cycles)
    dma_driver = DomainDriver(
        dut.DMA_MFB_SOF, dut.DMA_MFB_EOF, dut.DMA_MFB_EOF_POS, tb.pos_width,
        dut.DMA_MFB_SRC_RDY, dut.DMA_MFB_DST_RDY, None, dma_stims, traffic_cycles,
        mvb_sigs=(dut.DMA_MVB_VLD, dut.DMA_MVB_SRC_RDY, dut.DMA_MVB_DST_RDY))

    tb.pcie_clk.hook = pcie_driver.step
    dma_task = cocotb.start_soon(run_domain(dut.DMA_CLK, dma_driver, traffic_cycles))

    await dma_task

    cocotb.log.info("PHASE 2: idle, waiting for the last drain")

    # Three read-out periods of the slowest observed clock are enough for the
    # last events to reach the counter memory.
    await ClockCycles(dut.DMA_CLK, 3 * tb.drain_period)

    cocotb.log.info("PHASE 3: snapshot and check")

    await tb.snapshot()

    errors = 0
    for ep in range(tb.endpoints):
        for dma_side, stim in ((0, pcie_stims[ep]), (1, dma_stims[ep])):
            base = tb.stream_base(ep, dma_side)
            name = "dma" if dma_side else "pcie"
            for ch in range(1, stim.model.channels):
                got = await tb.read_counter(base + ch)
                exp = stim.model.cnt[ch]
                if got != exp:
                    cocotb.log.error(
                        f"ep{ep} {name} channel {ch}: expected {exp}, got {got}")
                    errors += 1

            cycles = await tb.read_counter(base + 0)
            assert cycles >= stim.model.cnt[0], \
                f"ep{ep} {name} cycle counter {cycles} below the driven {stim.model.cnt[0]}"

    assert errors == 0, f"{errors} counter mismatches"

    cocotb.log.info("PHASE 4: status registers")

    for ep in range(tb.endpoints):
        status = await tb.mi.read32(REG_PCIE_STATUS + 4 * ep)
        assert (status & 0x7) == 1, f"ep{ep} MPS {status & 0x7}"
        assert ((status >> 3) & 0x7) == 2, f"ep{ep} MRRS {(status >> 3) & 0x7}"
        assert (status >> 6) & 1 == 1, f"ep{ep} extended tag"
        assert (status >> 7) & 1 == 0, f"ep{ep} 10-bit tag"
        assert (status >> 8) & 1 == 1, f"ep{ep} RCB"
        assert (status >> 9) & 1 == 1, f"ep{ep} link up"

        tags = await tb.mi.read32(REG_PCIE_TAGS + 4 * ep)
        assert (tags & 0xFFFF) == 256, f"ep{ep} free tags {tags & 0xFFFF}"
        assert (tags >> 16) == 256, f"ep{ep} lowest free tags {tags >> 16}"

        stfifo = await tb.mi.read32(REG_PCIE_STFIFO + 4 * ep)
        assert (stfifo & 0xFFFF) == 1000, f"ep{ep} free FIFO words {stfifo & 0xFFFF}"
        assert (stfifo >> 16) == 1000, f"ep{ep} lowest free FIFO words {stfifo >> 16}"

    status = await tb.mi.read32(REG_STATUS)
    assert (status >> 1) & 1 == 0, "Deltas were lost"
    assert (status >> 2) & 1 == 0, "A drain overran"

    cocotb.log.info("PHASE 5: clear")

    await tb.clear()
    await tb.snapshot()
    for ep in range(tb.endpoints):
        for dma_side in (0, 1):
            base = tb.stream_base(ep, dma_side)
            channels = tb.dma_channels if dma_side else tb.pcie_channels
            for ch in range(1, channels):
                got = await tb.read_counter(base + ch)
                assert got == 0, f"Counter {base + ch} is {got} after clear"

    cocotb.log.info("PHASE 6: a reset of the MI domain alone")

    # The output FIFO of a probe is full while either of its two resets is
    # active. A probe must stay idle while the reporting domain is in reset.
    # Otherwise it would write into that FIFO and report a lost delta that
    # never happened.
    pcie_period = 2
    dut.MI_RESET.value = 1
    await Timer(2 * tb.drain_period * pcie_period, unit="ns")
    dut.MI_RESET.value = 0
    await ClockCycles(dut.MI_CLK, 5)
    await Timer(3 * tb.drain_period * pcie_period, unit="ns")

    status = await tb.mi.read32(REG_STATUS)
    assert (status >> 1) & 1 == 0, "An MI reset was reported as lost deltas"
    assert (status >> 2) & 1 == 0, "An MI reset was reported as a drain overrun"

    cocotb.log.info("PHASE 7: histograms of the resources that can run out")

    # The bands are one hot, so all the elapsed cycles must fall into exactly one
    # of them. Driving a resource to a known level must fill the matching band.
    async def check_hist(index, expected_band, label):
        for ep in range(tb.endpoints):
            base = tb.stream_base(ep, 0)
            first = (base + 1 + tb.pcie_buses * (5 + tb.pcie_regions)
                     + tb.pcie_driven_brakes + index * tb.hist_bands)

            bands = [await tb.read_counter(first + i) for i in range(tb.hist_bands)]
            cycles = await tb.read_counter(base)
            total = sum(bands)

            assert abs(total - cycles) <= 2 * tb.drain_period, \
                f"ep{ep} {label}: bands {bands} sum to {total}, {cycles} cycles elapsed"
            assert bands[expected_band] > 9 * total // 10, \
                f"ep{ep} {label}: expected band {expected_band}, got {bands}"

    # No tag left at all, and the storage FIFO down to an eighth of its words.
    for ep in range(tb.endpoints):
        dut.PCIE_TAG_FREE[ep].value = 0
        dut.PCIE_STFIFO_FREE[ep].value = tb.stfifo_capacity // 8

    # One read-out still carries old values. Let it reach the counters before
    # the clear, so that the measured window holds the new values alone.
    await Timer(2 * tb.drain_period * pcie_period, unit="ns")
    await tb.clear()
    await Timer(4 * tb.drain_period * pcie_period, unit="ns")
    await tb.snapshot()

    await check_hist(0, 0, "tag histogram")
    await check_hist(1, 1, "storage FIFO histogram")

    cocotb.log.info("DONE")
