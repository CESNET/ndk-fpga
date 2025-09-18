# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

# INFO
######
# This testbench measures maximal throughput of RX+TX DMA
# and produces graphs in app/build/card directory

import os
import sys
import logging
import cocotb
import itertools
from cocotb.triggers import Timer, Event, First, RisingEdge

from ndk_core import NFBDevice

import cocotbext.ofm.utils.sim.modelsim as ms
import cocotb.utils

from cocotbext.ofm.utils.sim.bus import MfbBus, MiBus, DmaUpMvbBus, DmaDownMvbBus


from ofm.comp.mfb_tools.debug.gen_loop_switch import GenLoopSwitch

# Configuration parameters
##########################

# used channels per DMA_ENDPOINT
USED_CHANNELS = {
    "RX": 16,
    "TX": 16,
}
# Max expected throughput (for graph generation)
PORT_THROUGHPUT = 100
PKTLEN = [x for x in range(64, 300) if x % 8 in [0, 1]]


logging.basicConfig(stream=sys.stderr, force=True)
logging.getLogger().setLevel(logging.INFO)

logger = logging.getLogger(__name__)

logger_mi = logging.getLogger("cocotb.nfb.ext.python_servicer")
#logger_mi.setLevel(logging.DEBUG)

# Shortcuts
e = cocotb.external
st = cocotb.utils.get_sim_time
add_cursor = ms.add_cursor
print = ms.print


def run_gnuplot(d, dev):
    file_path = os.path.realpath(__file__)[:-3] # crop the .py
    os.system(f'gnuplot -c "{file_path}.gpi" "{d}" "{os.getcwd()}/transcript" "{dev._card_name}" "{PORT_THROUGHPUT}G"')


async def get_dev(dut, init=True, **kwargs):
    dev = NFBDevice(dut, **kwargs)
    if init:
        await dev.init()
    return dev, dev.nfb


async def sendmsgs(txq, msgs):
    await e(txq.sendmsg)(msgs)


async def rx_push_descs(rxq, n, ev):
    burst = 64
    for i in range(n):
        pd = cocotb.start_soon(rxq._push_desc(flush=((i % burst) == (burst - 1))))
        evw = ev.wait()
        tr = await First(pd, evw)
        if tr == evw:
            return


async def recvmsgs(rxq, event):
    while not event.is_set():
        m = await e(rxq.recvmsg)()
        if m:
            pass
        else:
            await Timer(5, units='ns')


async def rx_stop_ch(rxq):
    await e(rxq.stop)()


async def wait_for_val(signal, val, clk, n, to=10000):
    re = RisingEdge(clk)
    i = 0
    while i != n:
        i = i + 1 if signal.value == val else 0
        await re
        to -= 1
        if to <= 0:
            raise TimeoutError()


def get_msg(pktlen, n, ch):
    return (bytes(itertools.chain([0, ch, (n >> 8) & 0xFF, (n) & 0xFF] * ((pktlen + 3) // 4)))[:pktlen], bytes(), 0)


def get_channel_list(tdir):
    EP_CHANNELS = getattr(core.dma_i, f"{tdir}_CHANNELS").value

    _chnls = min(USED_CHANNELS[tdir], EP_CHANNELS)
    chnls = []
    for ch in range(DMA_STREAMS * EP_CHANNELS):
        if ch % EP_CHANNELS < _chnls:
            chnls.append(ch)
    return _chnls, chnls


@cocotb.test(timeout_time=80000, timeout_unit='us', skip=False)
async def test_ndp_sendmsg_burst(dut):
    tdir = "TX"
    clk  = core.dma_i.USR_CLK
    re = RisingEdge(clk)
    bm = busm[tdir]
    for m in bm:
        cocotb.start_soon(m.monitor(clk))

    dev, nfb = await get_dev(dut)

    gls = []
    for i in range(DMA_STREAMS):
        gls.append(GenLoopSwitch(nfb, index=i))

    for g in gls:
        await e(setattr)(g.r2l, 'input', 2)

    stream_chnls, chnls = get_channel_list(tdir)
    tasks = []
    for pktlen in PKTLEN:
        for ch in chnls:
            await e(nfb.ndp.tx[ch].start)()

        for ch in chnls:
            npkts = min(256, 262144 // pktlen)
            msgs = [get_msg(pktlen, n, ch) for n in range(npkts)]
            t = cocotb.start_soon(sendmsgs(nfb.ndp.tx[ch], msgs))
            tasks.append((ch, t))

        for m in bm:
            await wait_for_val(m._get_handle('SRC_RDY'), 1, core.dma_i.USR_CLK, 1, 10000)
        for i in range(1000):
            await re

        #add_cursor(f"Measure start {pktlen}")
        for m in bm:
            m.clear()
        for i in range(2000):
            await re
        #add_cursor(f"Measure stop {pktlen}")

        mpps = PORT_THROUGHPUT * 1e3 / (8 * (pktlen + 24))
        eth_raw = (pktlen * mpps * 8)
        print("TXTHR:", pktlen, sum(m._thr * 1000 for m in bm), eth_raw)

        for ch, t in tasks:
            await t
        for ch, t in tasks:
            await e(nfb.ndp.tx[ch].stop)()

        for m in bm:
            await wait_for_val(m._get_handle('SRC_RDY'), 0, core.dma_i.USR_CLK, 150, 10000)
        tasks.clear()

    run_gnuplot(tdir, dev)


@cocotb.test(timeout_time=80000, timeout_unit='us', skip=False)
async def test_ndp_recvmsg_burst(dut):
    tdir = "RX"
    clk  = core.dma_i.USR_CLK
    re = RisingEdge(clk)
    bm = busm[tdir]
    for m in bm:
        cocotb.start_soon(m.monitor(clk))

    dev, nfb = await get_dev(dut)

    gls = []
    for i in range(DMA_STREAMS):
        gls.append(GenLoopSwitch(nfb, index=i))

    stop_channels = False
    channels_running = False

    stream_chnls, chnls = get_channel_list(tdir)
    tasks = []
    for pktlen in PKTLEN:
        if not channels_running:
            channels_running = True
            for ch in chnls:
                await e(nfb.ndp.rx[ch].start)()
                evd = Event()
                td = cocotb.start_soon(rx_push_descs(dev.dma.rx[ch], 2**24, evd))
                await re
                evr = Event()
                tr = cocotb.start_soon(recvmsgs(nfb.ndp.rx[ch], evr))
                tasks.append((ch, td, tr, evd, evr))

            for i in range(300):
                await re
        for g in gls:
            await e(g.l2r.gen_start)(True, pktlen, 0, stream_chnls)

        for m in bm:
            await wait_for_val(m._get_handle('SRC_RDY'), 1, core.dma_i.USR_CLK, 10, 10000)

        for i in range(1000):
            await re
        #add_cursor(f"Measure start {pktlen}")
        for m in bm:
            m.clear()
        for i in range(3000):
            await re
        #add_cursor(f"Measure stop {pktlen}")

        mpps = PORT_THROUGHPUT * 1e3 / (8 * (pktlen + 20))
        eth_raw = (pktlen * mpps * 8)
        print("RXTHR:", pktlen, sum(m._thr * 1000 for m in bm), eth_raw)

        for g in gls:
            await e(g.l2r.gen_stop)()

        for i in range(500):
            await re
        for m in bm:
            await wait_for_val(m._get_handle('SRC_RDY'), 0, core.dma_i.USR_CLK, 10000, 200000)

        for i in range(100):
            await re

        if stop_channels:
            channels_running = False

            tasks_stop = []
            for ch, td, tr, evd, evr in tasks:
                evd.set()
                await td
                evr.set()
                await tr
                t = cocotb.start_soon(rx_stop_ch(nfb.ndp.rx[ch]))
                tasks_stop.append(t)
            for t in tasks_stop:
                await t

    run_gnuplot(tdir, dev)


core = NFBDevice.core_instance_from_top(cocotb.top)
#ms.cmd(f"log -recursive {ms.cocotb2path(core)}/*")

DMA_STREAMS = core.dma_i.DMA_STREAMS.value

pcic = core.pcie_i.pcie_core_i
adapter = pcic.pcie_adapter_g[0].pcie_adapter_i

busm = {"RX": [], "TX": []}
for d in busm:
    for i in range(DMA_STREAMS):
        t = MfbBus(core.dma_i.gls_g[i].gls_en_g.gen_loop_switch_i, f'DMA_{d}_MFB', label=f"DMA_{d}_MFB{i}")
        t.add_wave()
        busm[d].append(t)

for i in range(core.dma_i.DMA_ENDPOINTS.value):
    DmaUpMvbBus(core.dma_i, 'PCIE_RQ_MVB', i, label=f"RQ_MVB_{i}").add_wave()
    MfbBus(core.dma_i, 'PCIE_RQ_MFB', i, label=f"RQ_MFB_{i}").add_wave()
    DmaDownMvbBus(core.dma_i, 'PCIE_RC_MVB', i, label=f"RC_MVB_{i}").add_wave()
    MfbBus(core.dma_i, 'PCIE_RC_MFB', i, label=f"RC_MFB_{i}").add_wave()

#for m in ["RC", "RQ", "CC", "CQ"]:
#    MfbBus(pcic, '{m}_MFB', 0).add_wave()

for i in range(core.pcie_i.PCIE_ENDPOINTS.value):
    MiBus(core.pcie_i, 'MI', i, label=f'MI_PCIe{i}').add_wave()
