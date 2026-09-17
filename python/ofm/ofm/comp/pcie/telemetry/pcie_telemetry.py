# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>

"""Reader and viewer of the PCIE_TELEMETRY_MI firmware component."""

import argparse
import json
import time
from typing import Any, Dict, List, Optional

import nfb
from tabulate import tabulate


# Names of the reasons why the PTC stops a stream, with the stream each reason
# stops. They are in the order of the bits of the BRAKE port of the component.
# The firmware says how many reasons it has. A reason added there later is
# reported under a generic name in the UP column until it is named here.
_BRAKE_NAMES = (
    ("UP", "no free PCIe tag"),
    ("UP", "PCIe tag not ready"),
    ("UP", "no room for completions"),
    ("UP", "no completion header entry"),
    ("DOWN", "MFB stalled towards DMA"),
    ("DOWN", "MVB stalled towards DMA"),
)

# Names of the histograms, in the order the probe keeps their bands, each with
# the configuration key that holds the capacity of the measured resource.
_HIST_NAMES = (
    ("PCIe tags", "tag_capacity"),
    ("PTC storage FIFO words", "stfifo_capacity"),
)

# Names of the histogram bands, from the exhausted resource upwards.
_BAND_NAMES = ("none", "<=1/8", "<=1/2", "rest")


class PcieTelemetry(nfb.BaseComp):
    """PCIe telemetry component class.

    The number of endpoints, the number of counters and their meaning are read
    from the configuration registers of the component. This class therefore
    works with any firmware configuration.
    """

    DT_COMPATIBLE = "cesnet,ofm,pcie_telemetry_mi"

    _REG_MAGIC = 0x0000
    _REG_VERSION = 0x0004
    _REG_TOPOLOGY = 0x0008
    _REG_LAYOUT = 0x000C
    _REG_CFG_PCIE = 0x0010
    _REG_CFG_DMA = 0x0014
    _REG_DRAIN = 0x0018
    _REG_CNT_BASE = 0x001C
    _REG_COMMAND = 0x0020
    _REG_STATUS = 0x0024
    _REG_READ_SEL = 0x0028
    _REG_CFG_REGIONS = 0x002C
    _REG_CFG_WIDTH = 0x0030
    _REG_CFG_WIDTH_DMA = 0x003C
    _REG_CFG_HIST = 0x0034
    _REG_CFG_CAPACITY = 0x0038
    _REG_PCIE_STATUS = 0x0040
    _REG_PCIE_TAGS = 0x0080
    _REG_PCIE_STFIFO = 0x00C0

    _CMD_SNAPSHOT = 1 << 0
    _CMD_CLEAR = 1 << 1
    _CMD_CLEAR_FLAGS = 1 << 2
    _CMD_CLEAR_MARKS = 1 << 3

    _MAGIC = 0x50544C4D
    _VERSION_MAJOR = 2

    def __init__(self, **kwargs):
        super().__init__(**kwargs)

        magic = self._comp.read32(self._REG_MAGIC)
        if magic != self._MAGIC:
            raise RuntimeError(f"Not a PCIe telemetry component, magic 0x{magic:08X}")

        version = self._comp.read32(self._REG_VERSION)
        self.version = (version >> 16, version & 0xFFFF)
        if self.version[0] != self._VERSION_MAJOR:
            raise RuntimeError(
                f"Telemetry major version {self.version[0]} is not "
                f"{self._VERSION_MAJOR}, the register map differs")

        topology = self._comp.read32(self._REG_TOPOLOGY)
        self.endpoints = topology & 0xFF
        self.dma_ports = (topology >> 8) & 0xFF

        layout = self._comp.read32(self._REG_LAYOUT)
        self.entries = layout & 0xFFFF
        self.cnt_width = (layout >> 16) & 0xFF
        self.ep_channels = (layout >> 24) & 0xFF

        cfg = self._comp.read32(self._REG_CFG_PCIE)
        self.pcie_channels = cfg & 0xFF
        self.pcie_buses = (cfg >> 8) & 0xFF
        self.pcie_regions = (cfg >> 16) & 0xFF
        self.pcie_brakes = (cfg >> 24) & 0xFF

        cfg = self._comp.read32(self._REG_CFG_DMA)
        self.dma_channels = cfg & 0xFF
        self.dma_buses = (cfg >> 8) & 0xFF
        self.dma_regions = (cfg >> 16) & 0xFF
        self.dma_brakes = (cfg >> 24) & 0xFF

        drain = self._comp.read32(self._REG_DRAIN)
        self.drain_period = drain & 0xFFFF
        self.item_bytes = (drain >> 16) & 0xFF
        self.cnt_base = self._comp.read32(self._REG_CNT_BASE)

        # Each bus has a geometry of its own. The probe of a clock domain is
        # built for the wider of its two buses. The counter layout therefore
        # uses pcie_regions and dma_regions, while the rates use the per bus
        # widths read here.
        width = self._comp.read32(self._REG_CFG_WIDTH)
        self.rq_region_bytes = width & 0xFFFF
        self.rc_region_bytes = (width >> 16) & 0xFFFF

        width = self._comp.read32(self._REG_CFG_WIDTH_DMA)
        self.up_region_bytes = width & 0xFFFF
        self.down_region_bytes = (width >> 16) & 0xFFFF

        regions = self._comp.read32(self._REG_CFG_REGIONS)
        self.rq_regions = regions & 0xFF
        self.rc_regions = (regions >> 8) & 0xFF
        self.up_regions = (regions >> 16) & 0xFF
        self.down_regions = (regions >> 24) & 0xFF

        hist = self._comp.read32(self._REG_CFG_HIST)
        self.hist_bands = hist & 0xFF
        self.pcie_hists = (hist >> 8) & 0xFF
        self.dma_hists = (hist >> 16) & 0xFF

        capacity = self._comp.read32(self._REG_CFG_CAPACITY)
        self.tag_capacity = capacity & 0xFFFF
        self.stfifo_capacity = (capacity >> 16) & 0xFFFF

        # The histogram bands are the last BRAKE channels of a probe.
        self.pcie_driven_brakes = self.pcie_brakes - self.pcie_hists * self.hist_bands
        self.dma_driven_brakes = self.dma_brakes - self.dma_hists * self.hist_bands

    # ------------------------------------------------------------------
    # Low level access
    # ------------------------------------------------------------------

    def _wait_idle(self, timeout: float = 1.0) -> None:
        deadline = time.time() + timeout
        while self._comp.read32(self._REG_STATUS) & 1:
            if time.time() > deadline:
                raise TimeoutError("The telemetry component stays busy")

    def snapshot(self) -> None:
        """Freezes a consistent copy of all counters for reading."""
        self._comp.write32(self._REG_COMMAND, self._CMD_SNAPSHOT)
        self._wait_idle()

    def clear(self) -> None:
        """Sets all counters, lowest values and flags to zero."""
        self._comp.write32(
            self._REG_COMMAND,
            self._CMD_CLEAR | self._CMD_CLEAR_FLAGS | self._CMD_CLEAR_MARKS)
        self._wait_idle()

    def clear_marks(self) -> None:
        """Starts a new measurement of the lowest free tags and FIFO words.

        The firmware keeps each lowest value until software clears it. Without
        this call the report would show the lowest value since the last full
        clear, instead of the lowest value of the measured interval.
        """
        self._comp.write32(self._REG_COMMAND, self._CMD_CLEAR_MARKS)

    def clear_flags(self) -> None:
        """Clears the error flags. The counters keep their values.

        The flags say that some deltas were lost. They stay set until software
        clears them, so a single event makes every later reading look invalid.
        The flags are cleared at the start of a measured interval, which makes
        them describe that interval only.
        """
        self._comp.write32(self._REG_COMMAND, self._CMD_CLEAR_FLAGS)

    @property
    def status(self) -> Dict[str, bool]:
        value = self._comp.read32(self._REG_STATUS)
        return {
            "busy": bool(value & 1),
            "lost_deltas": bool(value & 2),
            "readout_overrun": bool(value & 4),
        }

    def _read_counters(self) -> List[int]:
        """Reads the whole snapshot copy in as few bus transactions as possible."""
        raw = self._comp.read(self.cnt_base, 8 * self.entries)
        return [int.from_bytes(raw[8 * i:8 * i + 8], "little") for i in range(self.entries)]

    # ------------------------------------------------------------------
    # Decoding
    # ------------------------------------------------------------------

    def _bus_slice(self, counters: List[int], base: int, bus: int, stride: int,
                   regions: int, region_bytes: int, pcie_clk: bool,
                   has_mvb: bool, dma_up: bool) -> Dict:
        """Cuts out the counters of one bus. Stride is the width of the probe.

        The three flags describe the bus itself, not the traffic it carried.
        The report therefore never has to derive them from a counter that is
        zero for some other reason.
        """
        first = base + 1 + bus * (6 + stride)
        return {
            "words": counters[first + 0],
            "backpressure": counters[first + 1],
            "transactions": counters[first + 2],
            "mvb": counters[first + 3],
            "mvb_backpressure": counters[first + 4],
            "items": counters[first + 5],
            "regions": counters[first + 6:first + 6 + regions],
            "region_bytes": region_bytes,
            "pcie_clk": pcie_clk,
            "has_mvb": has_mvb,
            "dma_up": dma_up,
        }

    def read(self) -> Dict:
        """Takes a snapshot and returns all telemetry as a plain dictionary."""
        self.snapshot()
        counters = self._read_counters()

        result: Dict[str, Any] = {
            "endpoints": [],
            "status": self.status,
            "config": {
                "pcie_endpoints": self.endpoints,
                "dma_ports": self.dma_ports,
                "probe_pcie_regions": self.pcie_regions,
                "probe_dma_regions": self.dma_regions,
                "counter_width": self.cnt_width,
                "item_bytes": self.item_bytes,
                "drain_period": self.drain_period,
                "hist_bands": self.hist_bands,
                "tag_capacity": self.tag_capacity,
                "stfifo_capacity": self.stfifo_capacity,
            },
        }

        for ep in range(self.endpoints):
            pcie_base = ep * self.ep_channels
            dma_base = pcie_base + self.pcie_channels

            # The histograms belong to the PCIe clock probe. They are stored
            # after its BRAKE channels, in the order of the channels they
            # belong to.
            brakes = pcie_base + 1 + self.pcie_buses * (6 + self.pcie_regions)
            hists = brakes + self.pcie_driven_brakes

            reg = self._comp.read32(self._REG_PCIE_STATUS + 4 * ep)
            tags = self._comp.read32(self._REG_PCIE_TAGS + 4 * ep)
            stfifo = self._comp.read32(self._REG_PCIE_STFIFO + 4 * ep)

            # The PCIe side carries its headers inside the data stream, so only
            # the DMA side buses have an MVB of their own.
            buses = {
                "PTC -> PCIe (RQ)": self._bus_slice(
                    counters, pcie_base, 0, self.pcie_regions,
                    self.rq_regions, self.rq_region_bytes, True, False, False),
                "PCIe -> PTC (RC)": self._bus_slice(
                    counters, pcie_base, 1, self.pcie_regions,
                    self.rc_regions, self.rc_region_bytes, True, False, False),
            }
            for port in range(self.dma_ports):
                buses[f"DMA{port} -> PTC (UP)"] = self._bus_slice(
                    counters, dma_base, 2 * port, self.dma_regions,
                    self.up_regions, self.up_region_bytes, False, True, True)
                buses[f"PTC -> DMA{port} (DOWN)"] = self._bus_slice(
                    counters, dma_base, 2 * port + 1, self.dma_regions,
                    self.down_regions, self.down_region_bytes, False, True, False)

            result["endpoints"].append({
                "index": ep,
                "link_up": bool(reg >> 9 & 1),
                "mps": 128 << (reg & 0x7),
                "mrrs": 128 << (reg >> 3 & 0x7),
                "ext_tag": bool(reg >> 6 & 1),
                "tag_10b": bool(reg >> 7 & 1),
                "rcb": 128 if (reg >> 8 & 1) else 64,
                "tags_free": tags & 0xFFFF,
                "tags_free_min": tags >> 16,
                "stfifo_free": stfifo & 0xFFFF,
                "stfifo_free_min": stfifo >> 16,
                "pcie_cycles": counters[pcie_base],
                "dma_cycles": counters[dma_base],
                "brakes": counters[brakes:brakes + self.pcie_driven_brakes],
                "hists": [counters[hists + i * self.hist_bands:
                                   hists + (i + 1) * self.hist_bands]
                          for i in range(self.pcie_hists)],
                "buses": buses,
            })

        return result


def _diff(new: Dict, old: Optional[Dict]) -> Dict:
    """Subtracts two readings so that the result covers only the interval."""
    if old is None:
        return new

    out = json.loads(json.dumps(new))
    for ep_new, ep_old in zip(out["endpoints"], old["endpoints"]):
        for key in ("pcie_cycles", "dma_cycles"):
            ep_new[key] -= ep_old[key]
        ep_new["brakes"] = [a - b for a, b in zip(ep_new["brakes"], ep_old["brakes"])]
        ep_new["hists"] = [[a - b for a, b in zip(new_hist, old_hist)]
                           for new_hist, old_hist in zip(ep_new["hists"], ep_old["hists"])]
        for name, bus in ep_new["buses"].items():
            bus_old = ep_old["buses"][name]
            for key in ("words", "backpressure", "transactions", "mvb",
                        "mvb_backpressure", "items"):
                bus[key] -= bus_old[key]
            bus["regions"] = [a - b for a, b in zip(bus["regions"], bus_old["regions"])]
    return out


def _name(names: tuple, index: int, kind: str) -> str:
    """Names one channel, or describes it by its index when it has no name yet."""
    if index < len(names):
        return names[index]
    return f"{kind} {index}"


def _pct(part: int, whole: int) -> str:
    if whole == 0:
        return "   -  "
    return f"{100.0 * part / whole:6.2f}"


def format_report(data: Dict, seconds: Optional[float] = None) -> str:
    """Renders one reading as a human readable report."""
    cfg = data["config"]
    lines = []

    head = (f"PCIe telemetry - {cfg['pcie_endpoints']} endpoint(s), "
            f"{cfg['dma_ports']} DMA port(s) per endpoint")
    lines.append(head)
    lines.append("=" * len(head))
    lines.append(f"Measured over {seconds:.2f} s" if seconds
                 else "Totals since the last clear")

    flags = []
    if data["status"]["lost_deltas"]:
        flags.append("LOST DELTAS - the counters are not exact")
    if data["status"]["readout_overrun"]:
        flags.append("READ-OUT OVERRUN - the counters are not exact")
    if flags:
        lines.append("")
        for flag in flags:
            lines.append(f"  !! {flag}")

    for ep in data["endpoints"]:
        lines.append("")
        lines.append(f"PCIe endpoint {ep['index']}")
        lines.append("-" * 60)

        link = tabulate([
            ["Link", "up" if ep["link_up"] else "DOWN"],
            ["Max payload size (MPS)", f"{ep['mps']} B"],
            ["Max read request (MRRS)", f"{ep['mrrs']} B"],
            ["Extended tag (8-bit)", "on" if ep["ext_tag"] else "off"],
            ["10-bit tag", "on" if ep["tag_10b"] else "off"],
            ["Read completion boundary", f"{ep['rcb']} B"],
            ["PTC tags free", f"{ep['tags_free']} (lowest {ep['tags_free_min']})"],
            ["PTC storage FIFO free", f"{ep['stfifo_free']} words (lowest {ep['stfifo_free_min']})"],
        ], tablefmt="plain")
        lines.append(link)

        pcie_cycles = ep["pcie_cycles"]
        dma_cycles = ep["dma_cycles"]

        if seconds:
            lines.append("")
            lines.append(f"  PCIe clock {pcie_cycles / seconds / 1e6:.1f} MHz, "
                         f"DMA clock {dma_cycles / seconds / 1e6:.1f} MHz")

        rows = []
        for name, bus in ep["buses"].items():
            cycles = pcie_cycles if bus["pcie_clk"] else dma_cycles
            regions = len(bus["regions"])

            used = sum(bus["regions"])
            capacity = cycles * regions
            data_bytes = bus["items"] * cfg["item_bytes"]
            per_region = " ".join(f"{100.0 * r / cycles:.1f}" if cycles else "-"
                                  for r in bus["regions"])
            # Where the headers have an MVB bus of their own, every request
            # has an item there, so that is the whole transaction count. The
            # MFB carries only the requests that have payload.
            requests = bus["mvb"] if bus["has_mvb"] else bus["transactions"]

            gbps = ""
            mpps = ""
            if seconds:
                gbps = f"{data_bytes * 8 / seconds / 1e9:.2f}"
                mpps = f"{requests / seconds / 1e6:.3f}"

            # Only the bus towards the PTC carries both kinds of request, so
            # only there is the difference between the two counts the number of
            # reads. Every completion has payload, so on the other buses the
            # same subtraction would always give zero.
            read = "   -  "
            if bus["dma_up"]:
                read = _pct(max(requests - bus["transactions"], 0), requests)

            avg = "-"
            if bus["transactions"]:
                avg = f"{data_bytes / bus['transactions']:.0f}"

            mvb_stalled = "   -  "
            if bus["has_mvb"]:
                mvb_stalled = _pct(bus["mvb_backpressure"], cycles)

            rows.append([
                name,
                _pct(used, capacity),
                _pct(bus["words"], cycles),
                _pct(bus["backpressure"], cycles),
                mvb_stalled,
                per_region,
                gbps,
                mpps,
                read,
                avg,
            ])

        lines.append("")
        lines.append(tabulate(rows, headers=[
            "Bus", "Used %", "Words %", "MFB stall %", "MVB stall %",
            "Used per region %", "Gbps", "Mpps", "RD %", "Avg B",
        ], tablefmt="simple", disable_numparse=True))

        # The number of reasons comes from the firmware, so a reason added there
        # is reported even before it is named here. The last reason is not a
        # counter of its own. The stalled cycles of the RQ bus already say how
        # long the PCIe endpoint did not take data.
        brakes = [_BRAKE_NAMES[index] + (value,) if index < len(_BRAKE_NAMES)
                  else ("UP", f"reason {index}", value)
                  for index, value in enumerate(ep["brakes"])]
        brakes.append(("UP", "PCIe endpoint not ready",
                       ep["buses"]["PTC -> PCIe (RQ)"]["backpressure"]))

        # One column per stream, which keeps the block short.
        up = [(label, value) for stream, label, value in brakes if stream == "UP"]
        down = [(label, value) for stream, label, value in brakes if stream == "DOWN"]
        up_label = max((len(label) for label, _ in up), default=0) + 1
        down_label = max((len(label) for label, _ in down), default=0) + 1
        up_width = up_label + 8

        def cell(entries, index, width):
            if index >= len(entries):
                return ""
            return f"{entries[index][0]:<{width}}{_pct(entries[index][1], pcie_cycles)} %"

        lines.append("")
        lines.append("  Why the PCIe transfer stopped (share of PCIe clock cycles)")
        head = f"    {'UP stream':<{up_width}}"
        lines.append((head + "    DOWN stream" if down else head).rstrip())
        for index in range(max(len(up), len(down))):
            left = cell(up, index, up_label)
            right = cell(down, index, down_label)
            lines.append(f"    {left:<{up_width}}    {right}".rstrip())

        # How long a resource was short, not only how low it once got. The bands
        # are shares of the capacity, so one table serves every resource.
        hist_rows = []
        for index, bands in enumerate(ep["hists"]):
            title = _name(tuple(name for name, _ in _HIST_NAMES), index, "resource")
            capacity = 0
            if index < len(_HIST_NAMES):
                capacity = cfg.get(_HIST_NAMES[index][1], 0)
            hist_rows.append([title, str(capacity) if capacity else "-"]
                             + [_pct(value, pcie_cycles) for value in bands])

        if hist_rows:
            lines.append("")
            lines.append(tabulate(hist_rows, headers=["Time spent low", "of"] + [
                _name(_BAND_NAMES, band, "band")
                for band in range(cfg["hist_bands"])
            ], tablefmt="simple", disable_numparse=True))

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        prog="nfb-pcie-telemetry",
        description="Reads and shows the PCIe infrastructure telemetry of the NDK firmware.")
    parser.add_argument("-d", "--device", default=nfb.libnfb.Nfb.default_dev_path,
                        help="path to the NFB device")
    parser.add_argument("-i", "--index", type=int, default=0,
                        help="index inside DevTree")
    parser.add_argument("-t", "--interval", type=float, default=1.0,
                        help="length of the measured interval in seconds, "
                             "0 shows the totals since the last clear")
    parser.add_argument("-w", "--watch", action="store_true",
                        help="keep measuring and printing until interrupted")
    parser.add_argument("-c", "--clear", action="store_true",
                        help="zero all counters and exit")
    parser.add_argument("-j", "--json", action="store_true",
                        help="print the raw values as JSON instead of a table")
    args = parser.parse_args()

    telemetry = PcieTelemetry(dev=args.device, index=args.index)

    if args.clear:
        telemetry.clear()
        print("Counters cleared.")
        return

    def measure():
        if args.interval <= 0:
            return telemetry.read(), None
        telemetry.clear_flags()
        telemetry.clear_marks()
        first = telemetry.read()
        start = time.time()
        time.sleep(args.interval)
        second = telemetry.read()
        return _diff(second, first), time.time() - start

    while True:
        data, seconds = measure()
        if args.json:
            print(json.dumps({"seconds": seconds, "data": data}, indent=4))
        else:
            print(format_report(data, seconds))
        if not args.watch:
            break
        print()


if __name__ == "__main__":
    main()
