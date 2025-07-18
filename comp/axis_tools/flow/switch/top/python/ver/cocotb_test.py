# cocotb_test.py: Switch verification environment
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Tomas Hak <hak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from switch import Switch

from random import randbytes, randint

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles, with_timeout

from cocotbext.ofm.mi.drivers import MIRequestDriver
from cocotbext.axi import AxiStreamFrame, AxiStreamBus, AxiStreamSource, AxiStreamSink, AxiStreamMonitor

from scapy.all import Ether, Dot1Q, raw
#import json


class testbench:
    """ Test environment. """

    def __init__(self, dut, debug=False):
        """ Constructor.

            Params
            ------
                dut   ... DUT object
                debug ... log-level modifier
        """
        # DUT info
        self.dut       = dut
        self.num_ports = dut.NUM_PORTS.value

        # IFC (MI, AXI-Stream) drivers
        self.mi_driver = MIRequestDriver(dut, "MI", dut.CLK)
        self.rx_axi_drivers = [
            AxiStreamSource(AxiStreamBus.from_prefix(dut, "RX_AXI", array_idx=p), dut.CLK, dut.RESET)
            for p in range(self.num_ports)
        ]
        self.tx_axi_drivers = [
            AxiStreamSink(AxiStreamBus.from_prefix(dut, "TX_AXI", array_idx=p), dut.CLK, dut.RESET)
            for p in range(self.num_ports)
        ]
        self.rx_axi_monitors = [
            AxiStreamMonitor(AxiStreamBus.from_prefix(dut, "RX_AXI", array_idx=p), dut.CLK, dut.RESET)
            for p in range(self.num_ports)
        ]

        # Golden Model
        self.switch = Switch(grm=True)
        self.tx_predict = [[] for _ in range(self.num_ports)]
        self.tx_frames  = [[] for _ in range(self.num_ports)]

        # set DEBUG log level
        loglevel = cocotb.logging.DEBUG if debug else cocotb.logging.WARNING
        self.mi_driver.log.setLevel(loglevel)
        for p in range(self.num_ports):
            self.rx_axi_drivers[p].log.setLevel(loglevel)
            self.tx_axi_drivers[p].log.setLevel(loglevel)

    async def reset(self):
        """ Perform firmware reset. """
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)

    async def init(self):
        """ Initialize and configure the switch. """

        await self.switch.init(read_f=self.mi_driver.read, write_f=self.mi_driver.write)
        await self.switch.clear_all()

        cfg = {
            self.switch.mats[0][0]: {
                0x20: [[0x01, 0x15, 0x00, 0x00, 0x04], [0x01, 0x37, 0x00, 0x00, 0x05], [0x01]],
                0x21: [[0x01], [0x03], [0x01]],
                0x22: [[0x02], [0x03], [0x02]],
                0x23: [[0x03], [0x03], [0x03]]
            },
            self.switch.mats[0][1]: {
                0x20: [[0x31, 0x02], [0xff, 0x0f], [0x01]],
                0x21: [[0x32, 0x02], [0xff, 0x0f], [0x00]]
            },
            self.switch.mats[1][0]: {
                0x20: [[0x01], [0x03], [0x01]],
                0x22: [[0x02], [0x03], [0x02]],
                0x23: [[0x03], [0x03], [0x03]]
            },
            self.switch.mats[2][0]: {
                0x20: [[0x01], [0x03], [0x01]],
                0x22: [[0x02], [0x03], [0x02]],
                0x23: [[0x03], [0x03], [0x03]]
            },
            self.switch.mats[3][0]: {
                0x20: [[0x01], [0x03], [0x01]],
                0x22: [[0x02], [0x03], [0x02]],
                0x23: [[0x03], [0x03], [0x03]]
            },
        }
        await self.switch.config(cfg)
        await self.switch.wait()

    def reset_frames(self):
        """ Reset frames lists. """
        self.tx_predict = [[] for _ in range(self.num_ports)]
        self.tx_frames  = [[] for _ in range(self.num_ports)]

    async def monitor_rx_port(self, port, dest):
        """ Update frame's sim_time_start after sending on RX bus.

            Params
            ------
                port ... input port
                dest ... predicted output port
        """
        frame = await self.rx_axi_monitors[port].recv()
        index = self.tx_predict[dest].index(frame)
        self.tx_predict[dest][index].sim_time_start = frame.sim_time_start

    async def send_frames(
                self, *, count: int = None, port: int = None, frames: list[Ether] = [], length: int = None,
                cleanup: bool = True, fullspeed: bool = True
            ) -> dict:
        """ Generate frames to DUT's RX.

            Params
            ------
                count     ... number of frames
                port      ... input port
                frames    ... frames list (in scapy.all.Ether format)
                length    ... length of frames
                cleanup   ... reset frames lists after test done
                fullspeed ... do not generate inter-frame gaps

            Yields
            ------
                dict      ... information about the generated frame
        """
        # adjust frames count
        count          = len(frames) if count is None else count
        default_port   = port
        default_length = length
        for f in range(count):
            # adjust port number
            port = randint(0, self.num_ports-1) if default_port is None else default_port
            # make adjustments for frame replay
            if frames:
                f_idx  = f % len(frames)
                length = len(frames[f_idx]) if default_length is None else default_length
                frame  = frames[f_idx]
                if length > len(frame):
                    frame /= randbytes(length-len(frame))
            # make adjustments for random frame generation
            if not frames:
                length = randint(60, 1500) if default_length is None else max(default_length, 14)
                frame  = Ether(dst=randbytes(6), src=randbytes(6))/randbytes(length-14)
            # log and send frame
            axi_frame = AxiStreamFrame(raw(frame))
            dest      = self.switch.predict(frame, port)
            self.tx_predict[dest].append(axi_frame)
            await self.rx_axi_drivers[port].send(axi_frame)
            if not fullspeed:
                await self.rx_axi_drivers[port].wait()
            yield {'ip': port, 'op': dest, 'scapy': frame, 'axis': axi_frame, 'length': length}

        await self.check_frames()
        if cleanup:
            self.reset_frames()

    async def recv_frames(self):
        """ Receive frames from DUT's TX. """
        for op, frames in enumerate(self.tx_predict):
            for _ in frames:
                try:
                    await with_timeout(self.tx_axi_drivers[op].wait(), 1, 'ms')
                    self.tx_frames[op].append(await with_timeout(self.tx_axi_drivers[op].recv(), 100, 'ns'))
                except cocotb.result.SimTimeoutError:
                    cocotb.log.warning("No frame has arrived!")

    async def check_frames(self):
        """ Check received frames against predicted outputs. """
        await self.recv_frames()
        for op, frames in enumerate(self.tx_predict):
            real, pred = self.tx_frames[op].copy(), []

            # check difference
            for frame in frames:
                if frame in real:
                    real.remove(frame)
                else:
                    pred.append(frame)

            # report mismatch
            if pred:
                cocotb.log.error(f"{len(pred)} frame(s) didn't arrive:")
                for frame in pred:
                    cocotb.log.error(f"\t{frame.sim_time_end} : {[hex(val) for val in frame.tdata]}")
            if real:
                cocotb.log.error(f"{len(real)} frame(s) shouldn't arrive:")
                for frame in real:
                    cocotb.log.error(f"\t{frame.sim_time_end} : {[hex(val) for val in frame.tdata]}")


def report_throughput(silent, start, end, ip_bytes, op_bytes) -> float:
    """ Report throughput measurements.

        Params
        ------
            silent   ... do not send output to cocotb.log
            start    ... test start simulation time
            end      ... test end simulation time
            ip_bytes ... list with bytes sent per input port
            op_bytes ... list with bytes received per output port

        Returns
        -------
            float    ... average throughput of input/output ports
    """
    duration = end - start
    port_str = ["Input ports ", "Output ports"]
    byte_arr = [ip_bytes, op_bytes]
    result   = 0
    for i in range(2):
        if not silent:
            cocotb.log.info(f"{port_str[i]}: throughput [Gb/s]")
        for port in range(len(byte_arr[i])):
            throughput = round((byte_arr[i][port] * 8) / (duration / 1_000), 2)
            result    += throughput
            if not silent:
                cocotb.log.info(f"{port:<{len(port_str[i])}}: {throughput}")
    return round(result/(len(ip_bytes)+len(op_bytes)), 2)


def report_latency(silent, tb: testbench) -> dict:
    """ Report latency measurements.

        Params
        ------
            testbench ... test environment

        Returns
        -------
            dict      ... information about measured latency (min, max, avg)
    """
    latency_min = 1000
    latency_max = 0
    latency_sum = 0
    num_frames  = 0
    for op, pr_frames in enumerate(tb.tx_predict):
        for pr_frame in pr_frames:
            r_frame      = tb.tx_frames[op][tb.tx_frames[op].index(pr_frame)]
            latency      = (r_frame.sim_time_start - pr_frame.sim_time_start) / 1000
            latency_min  = min(latency_min, latency)
            latency_max  = max(latency_max, latency)
            latency_sum += latency
            num_frames  += 1
    if not silent:
        cocotb.log.info("Latency [ns]:")
        cocotb.log.info(f"Min         : {latency_min}")
        cocotb.log.info(f"Max         : {latency_max}")
        cocotb.log.info(f"Avg         : {round(latency_sum/num_frames, 2)}")
    return {'min': latency_min, 'max': latency_max, 'avg': round(latency_sum/num_frames, 2)}


async def run_test(
            tb: testbench, test_title: str, measure: bool, silent: bool = False, *,
            c: int = None, p: int = None, f: list[Ether] = [], n: int = None,
            cl: bool = True, fs: bool = True
        ) -> dict:

    """ Perform DUT test.

        Params
        ------
            testbench          ... test environment
            test_title         ... name of test
            measure            ... perform throughput and latency measurements?
            silent             ... do not send output to cocotb.log
            c, p, f, n, cl, fs ... see testbench.send_frames

        Returns
        -------
            dict               ... measurements
    """

    measurements = {'throughput': 0, 'latency': {}}
    if not silent:
        cocotb.log.info(f"\n--- {test_title} ---\n")
    if (measure):
        num_bytes_ip = [0 for _ in range(tb.num_ports)]
        num_bytes_op = [0 for _ in range(tb.num_ports)]
        start = cocotb.utils.get_sim_time()
        async for frame in tb.send_frames(count=c, port=p, frames=f, length=n, cleanup=False, fullspeed=fs):
            length = frame['length']
            num_bytes_ip[frame['ip']] += length
            num_bytes_op[frame['op']] += length
            cocotb.start_soon(tb.monitor_rx_port(frame['ip'], frame['op']))
        if not silent:
            cocotb.log.info("--- Measurements ---")
        measurements['throughput'] = report_throughput(silent, start, cocotb.utils.get_sim_time(), num_bytes_ip, num_bytes_op)
        measurements['latency']    = report_latency(silent, tb)
        if (cl):
            tb.reset_frames()

    else:
        async for frame in tb.send_frames(count=c, port=p, frames=f, length=n, cleanup=cl, fullspeed=fs):
            cocotb.start_soon(tb.monitor_rx_port(frame['ip'], frame['op']))
    return measurements


@cocotb.test
async def run_tests(dut):
    """ Main verification function. """

    cocotb.start_soon(Clock(dut.CLK, 5, units="ns").start())
    tb = testbench(dut)
    await tb.reset()
    await tb.init()

    frames_vlan = [
        Ether(dst="00:5d:00:00:06:00")/Dot1Q(vlan=561),
        Ether(dst="01:15:00:00:04:00")/Dot1Q(vlan=562)
    ]
    frames_all2one = [Ether(dst="04:00:00:00:00:00")]

    await run_test(tb, "VLAN switching - priority"                    , False, c=10   , p=0, f=frames_vlan)
    await run_test(tb, "Ethernet switching - small frames (64B)"      , True , c=10000, n=64)
    await run_test(tb, "Ethernet switching - medium frames (256B)"    , True , c=10000, n=256)
    await run_test(tb, "Ethernet switching - larger frames (512B)"    , True , c=10000, n=512)
    await run_test(tb, "Ethernet switching - large frames (1500B)"    , True , c=10000, n=1500)
    await run_test(tb, "Ethernet switching - non-full throughput"     , True , c=10000, fs=False)
    await run_test(tb, "Ethernet switching - random frames (60-1500B)", True , c=10000)
    await run_test(tb, "Ethernet switching - all-to-one"              , True , c=10000, f=frames_all2one, n=64)

#    measurements = []
#    for length in range(60, 1500, 4):
#        measurements.append(await run_test(tb, "", True, True, c=10000, n=length))
#    with open("results.json", "w") as f:
#        f.write(json.dumps(measurements))
