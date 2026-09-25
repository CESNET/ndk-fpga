#!/usr/bin/env python3
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
"""Automated DMA throughput sweep and FW-to-FW comparison, built on top of gls_mod.py.

Drives gls_mod.py for the four DMA scenarios (RX DMA only, TX DMA only, RX+TX DMA
independent, RX+TX DMA connected through a SW loopback) across a range of frame
lengths, tags each run with the FW build identity read from the Device Tree, and
plots the results. Every chart shows the bit rate in Gbps and the frame rate in Mpps.
A separate "compare" mode overlays several such runs (e.g. two different FW builds) on
common charts, which shows how the throughput changed between FW versions.

Two-step workflow:
    ./dma_throughput_sweep.py run     -d /dev/nfb0 -o results/
    ./dma_throughput_sweep.py compare results/<fw_id_A> results/<fw_id_B>
"""

import argparse
import csv
import datetime
import re
import socket
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Dict, List, Mapping, Optional, Tuple

# numpy, pandas and matplotlib all come with the "ofm" Python package (ndk-fpga/python/ofm).
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

matplotlib.use("Agg") # headless: charts are written to files, never shown in a window

# The "nfb" package (and with it the access to the card and the Device Tree) is not
# imported here. The "run" subcommand imports it only when it needs it, see
# default_device_path() and read_fw_metadata(). The "compare" subcommand then works on
# saved CSVs on a workstation that has no card and no nfb package installed.


# ==============================================================================
# Shared constants
# ==============================================================================

# The four DMA scenarios this script automates, mapped onto gls_mod.py's own
# "-m/--mode" values so measurement logic (mux config, speed meters, NDP tools)
# lives in exactly one place.
DMA_MODES = ["dma_rx", "dma_tx", "dma_rxtx", "dma_swloop"]

MODE_LABELS = {
    "dma_rx": "RX DMA only",
    "dma_tx": "TX DMA only",
    "dma_rxtx": "RX+TX DMA independent",
    "dma_swloop": "RX+TX DMA (SW loopback)",
}

# Categorical palette, fixed order (not cycled) so a given mode/run always maps to
# the same color across plots. First 4 slots reused for the 4 DMA modes; the full
# 8 are available as the categorical order when "compare" overlays multiple runs.
CATEGORICAL_PALETTE = [
    "#2a78d6",  # blue
    "#eb6834",  # orange
    "#1baf7a",  # aqua
    "#eda100",  # yellow
    "#e87ba4",  # magenta
    "#008300",  # green
    "#4a3aa7",  # violet
    "#e34948",  # red
]

MODE_COLORS = dict(zip(DMA_MODES, CATEGORICAL_PALETTE))

CHART_STYLE = {
    "surface": "#fcfcfb",
    "ink_primary": "#0b0b0b",
    "ink_secondary": "#52514e",
    "ink_muted": "#898781",
    "gridline": "#e1e0d9",
    "baseline": "#c3c2b7",
}

METADATA_PREFIX = "#meta:"

# The two measured directions. Each name is also the prefix of its result columns.
DIRECTIONS = [("rx", "RX DMA"), ("tx", "TX DMA")]


def frames_per_second(bps: float, length_bytes: float) -> float:
    """Convert a bit rate into a frame rate for frames of the given length.

    gls_mod.py reports the bit rate of whole frames, so one frame takes exactly
    8 * length_bytes bits. Both values come from the same result row.
    """
    return bps / (8 * length_bytes)


@dataclass(frozen=True)
class Metric:
    """One measured quantity, drawn in its own row of chart panels."""
    key: str                                  # suffix of the result column, e.g. "rx_bps"
    panel_title: str                          # completes the panel title after the direction
    axis_label: str
    scale: float                              # divides the stored value to get the axis unit
    legend_loc: str                           # corner the curves leave free for this metric
    from_bps: Callable[[float, float], float] # derives the metric from a bit rate


METRICS = [
    Metric("bps", "throughput", "Throughput [Gbps]", 1e9, "lower right", lambda bps, length: bps),
    Metric("pps", "frame rate", "Frame rate [Mpps]", 1e6, "upper right", frames_per_second),
]

# Below this number of points every curve also gets a marker per point. A line through
# a single point draws nothing, and a sweep of a few lengths reads better as points.
MARKED_POINTS_LIMIT = 16


def point_marker(point_count: int) -> Optional[str]:
    return "o" if point_count <= MARKED_POINTS_LIMIT else None


# ==============================================================================
# FW / device identity
# ==============================================================================

@dataclass
class FwMetadata:
    card_name: str
    project_name: Optional[str] = None
    project_variant: Optional[str] = None
    project_version: Optional[str] = None
    build_revision: Optional[str] = None
    build_author: Optional[str] = None
    build_tool: Optional[str] = None
    build_time: Optional[int] = None
    label_override: Optional[str] = None

    @property
    def build_time_iso(self) -> Optional[str]:
        if self.build_time is None:
            return None
        return datetime.datetime.fromtimestamp(self.build_time).strftime("%Y-%m-%d_%H-%M-%S")

    @property
    def fw_id(self) -> str:
        """A short, filesystem-safe identifier used to tag/group a run's output."""
        if self.label_override:
            slug = self.label_override
        else:
            parts = [self.card_name]
            if self.project_name:
                parts.append(self.project_name)
            if self.project_variant:
                parts.append(self.project_variant)
            parts.append(self.build_revision or self.build_time_iso or "unknown_build")
            slug = "_".join(parts)
        return re.sub(r"[^A-Za-z0-9._-]+", "-", slug)

    @property
    def label(self) -> str:
        """A short human-readable label used in chart legends."""
        if self.label_override:
            return self.label_override
        parts = [self.project_name or self.card_name]
        if self.project_variant:
            parts.append(self.project_variant)
        if self.build_revision:
            parts.append(self.build_revision)
        elif self.build_time_iso:
            parts.append(self.build_time_iso)
        return " ".join(parts)

    def as_dict(self) -> Dict[str, str]:
        return {
            "card_name": self.card_name,
            "project_name": self.project_name or "",
            "project_variant": self.project_variant or "",
            "project_version": self.project_version or "",
            "build_revision": self.build_revision or "",
            "build_author": self.build_author or "",
            "build_tool": self.build_tool or "",
            "build_time": str(self.build_time) if self.build_time is not None else "",
            "build_time_iso": self.build_time_iso or "",
            "label": self.label,
        }


def default_device_path() -> str:
    """The device path the nfb library itself defaults to (usually /dev/nfb0).

    Resolved on demand rather than as an argparse default, because merely building the
    parser must not require the nfb package - see the note next to the imports.
    """
    import nfb
    return nfb.default_dev_path


def read_fw_metadata(device_path: str) -> FwMetadata:
    """Read FW build identity from the Device Tree "firmware" node.

    Only "card-name" is guaranteed to be present; the rest are best-effort and
    depend on the build system having recorded them (see build/DevTree.tcl and
    core/top/DevTree.tcl).
    """
    import nfb
    fw_node = nfb.Nfb(device_path).fdt.get_node("firmware")

    def prop(name: str) -> Optional[str]:
        if fw_node.exist_property(name):
            return str(fw_node.get_property(name).value)
        return None

    build_time = prop("build-time")
    return FwMetadata(
        card_name=prop("card-name") or "unknown-card",
        project_name=prop("project-name"),
        project_variant=prop("project-variant"),
        project_version=prop("project-version"),
        build_revision=prop("build-revision"),
        build_author=prop("build-author"),
        build_tool=prop("build-tool"),
        build_time=int(build_time) if build_time else None,
    )


# ==============================================================================
# "run" subcommand: drive gls_mod.py across modes and frame sizes
# ==============================================================================

@dataclass
class RunParams:
    device: str
    modes: List[str]
    size_min: int
    size_max: int
    size_step: int
    channels: Optional[str]
    index: Optional[str]
    cycles: int
    frequency: int
    rate_layer: int
    ext_loop: bool
    buffer_count: Optional[int]
    buffer_size: Optional[int]
    eth_rate: Optional[int]

    def chart_config(self) -> Dict[str, object]:
        """The settings shown in the chart subtitle, keyed exactly like the metadata
        written into the results CSV. A fresh run and a run reloaded from disk can
        therefore share format_config_subtitle()."""
        return {
            "channels": self.channels,
            "cycles": self.cycles,
            "frequency": self.frequency,
            "rate_layer": self.rate_layer,
            "buffer_count": self.buffer_count,
            "buffer_size": self.buffer_size,
            "eth_rate": self.eth_rate,
        }


def parse_frame_size(values: List[int]) -> Tuple[int, int, int]:
    """Read the "-s" argument as one frame length, or as a MIN MAX STEP sweep."""
    if len(values) == 1:
        return values[0], values[0], 1
    if len(values) == 3:
        return values[0], values[1], values[2]
    sys.exit("ERROR: -s takes either a single frame length, or three values: MIN MAX STEP")


# Rough packet size above which the default kernel DMA buffer size tends to be too small to fit
# a whole packet into a single descriptor (MTU/jumbo-sized packets). The exact default depends on
# the DMA driver/build, so this is only used for an advisory warning, not enforced.
JUMBO_PACKET_SIZE_WARN = 4096


def configure_dma_buffers(device: str, buffer_count: Optional[int], buffer_size: Optional[int]) -> None:
    """Set the kernel DMA buffer count/size via 'nfb-dma' (DMA Medusa only) before the sweep.

    The setting is global for the driver, not limited to one direction or channel range. It
    stays set after this script exits and affects every other process using the card. It needs
    root privileges, so 'sudo' is called without capturing its output. The user can then enter
    the password when 'sudo' asks for it.
    """
    if buffer_size is None:
        print(f"NOTE: --buffer-size is not set. The current kernel DMA buffer size stays. "
              f"For MTU/jumbo-sized packets (roughly {JUMBO_PACKET_SIZE_WARN} B and up) the "
              f"default size is usually too small for a whole packet in a single DMA descriptor. "
              f"Pass --buffer-size large enough for the largest packet you will send.")
    elif buffer_size < JUMBO_PACKET_SIZE_WARN:
        print(f"WARNING: --buffer-size {buffer_size} may be too small for MTU/jumbo-sized packets "
              f"(roughly {JUMBO_PACKET_SIZE_WARN} B and up). Such packets do not fit into a single "
              f"DMA descriptor and are dropped or truncated.")

    cmd = ["sudo", "nfb-dma", "-d", device]
    if buffer_count is not None:
        cmd += ["-C", str(buffer_count)]
    if buffer_size is not None:
        cmd += ["-B", str(buffer_size)]

    print(f"\n==== Configuring DMA buffers ====\n$ {' '.join(cmd)}")
    result = subprocess.run(cmd)
    if result.returncode != 0:
        raise RuntimeError(f"'nfb-dma' buffer configuration failed (exit code {result.returncode})")


def run_gls_mode(gls_mod_path: Path, mode: str, params: RunParams, workdir: Path) -> Path:
    """Invoke gls_mod.py for a single mode and return the path to its report CSV."""
    workdir.mkdir(parents=True, exist_ok=True)
    # Remove what a previous sweep left here, so the report CSV and the NDP logs read
    # afterwards can only describe this run.
    for old_file in list(workdir.glob("report_*.csv")) + list(workdir.glob("ndp-*.log")):
        old_file.unlink()

    cmd = [
        sys.executable, str(gls_mod_path),
        "-d", params.device,
        "-m", mode,
        "-s", str(params.size_min), str(params.size_max), str(params.size_step),
        "-C", str(params.cycles),
        "-f", str(params.frequency),
        "-r", str(params.rate_layer),
        "-l",
    ]
    if params.channels:
        cmd += ["-c", params.channels]
    if params.index:
        cmd += ["-i", params.index]
    if params.ext_loop:
        cmd += ["-e"]

    print(f"\n==== Running gls_mod.py mode '{mode}' ({MODE_LABELS[mode]}) ====")
    print("$ " + " ".join(cmd))
    result = subprocess.run(cmd, cwd=workdir)
    if result.returncode != 0:
        raise RuntimeError(f"gls_mod.py failed for mode '{mode}' (exit code {result.returncode})")

    reports = list(workdir.glob("report_*.csv"))
    if len(reports) != 1:
        raise RuntimeError(
            f"Expected exactly one report_*.csv from gls_mod.py in {workdir}, found {len(reports)}"
        )
    return reports[0]


def load_mode_report(csv_path: Path, mode: str) -> "pd.DataFrame":
    """Load one gls_mod.py report, renaming its columns to this script's short names."""
    df = pd.read_csv(csv_path)
    df = df.rename(columns={"Length": "length", "TX APP speed": "tx_bps", "RX APP speed": "rx_bps"})
    df["mode"] = mode
    return add_frame_rate_columns(df[["mode", "length", "tx_bps", "rx_bps"]])


def add_frame_rate_columns(df: "pd.DataFrame") -> "pd.DataFrame":
    """Add the frame rate columns derived from the measured bit rate and frame length."""
    for direction, _ in DIRECTIONS:
        df[f"{direction}_pps"] = frames_per_second(df[f"{direction}_bps"], df["length"])
    return df


def write_results_csv(df: "pd.DataFrame", meta: FwMetadata, params: RunParams, out_path: Path) -> None:
    """Write one self-describing CSV: "#meta:" rows, a blank separator line, then the data.

    Keeping the run's identity and settings in the same file is what lets "compare"
    label the curves and warn about runs that are not comparable.
    """
    out_path.parent.mkdir(parents=True, exist_ok=True)
    meta_rows = {
        **meta.as_dict(),
        "modes": ",".join(params.modes),
        "size_min": params.size_min,
        "size_max": params.size_max,
        "size_step": params.size_step,
        "channels": params.channels or "all",
        "cycles": params.cycles,
        "frequency": params.frequency,
        "rate_layer": params.rate_layer,
        "buffer_count": params.buffer_count if params.buffer_count is not None else "default",
        "buffer_size": params.buffer_size if params.buffer_size is not None else "default",
        "eth_rate": params.eth_rate if params.eth_rate is not None else "",
        "hostname": socket.gethostname().partition(".")[0],
        "run_time_iso": datetime.datetime.now().strftime("%Y-%m-%d_%H-%M-%S"),
    }
    with open(out_path, "w", newline="") as f:
        writer = csv.writer(f)
        for key, value in meta_rows.items():
            writer.writerow([f"{METADATA_PREFIX}{key}", value])
        f.write("\n")
    df.to_csv(out_path, mode="a", index=False)


def read_results_csv(path: Path) -> Tuple["pd.DataFrame", Dict[str, str]]:
    """Read back a file written by write_results_csv(); returns its data and metadata."""
    meta: Dict[str, str] = {}
    data_start = 0
    with open(path, newline="") as f:
        for i, row in enumerate(csv.reader(f)):
            if row and row[0].startswith(METADATA_PREFIX):
                meta[row[0][len(METADATA_PREFIX):]] = row[1] if len(row) > 1 else ""
            elif not row:
                data_start = i + 1
                break
    df = pd.read_csv(path, skiprows=data_start)
    if "rx_pps" not in df.columns:
        # A results file written before the frame rate was added holds bit rates only.
        add_frame_rate_columns(df)
    return df, meta


def has_data(series: "pd.Series") -> bool:
    """True if a throughput series looks like a real measurement rather than an
    unmeasured direction. gls_mod.py reports a constant 0 for a direction a mode
    doesn't use (e.g. the tx_bps column for "dma_rx"), which would otherwise be
    plotted as a flat zero line indistinguishable from an actual regression."""
    return bool((series.fillna(0) != 0).any())


def finish_axes(ax, title: str, metric: Metric) -> None:
    ax.set_title(title, color=CHART_STYLE["ink_primary"], fontsize=12, loc="left")
    ax.set_xlabel("Frame length [B]")
    ax.set_ylabel(metric.axis_label)
    # Start at zero and keep a gap above the highest curve, so a marker is never cut.
    ax.set_ylim(0, ax.get_ylim()[1] * 1.05)
    if ax.get_legend_handles_labels()[1]:
        ax.legend(frameon=False, loc=metric.legend_loc, fontsize=9)
    else:
        ax.text(0.5, 0.5, "No data for this direction in any selected mode",
                transform=ax.transAxes, ha="center", va="center",
                color=CHART_STYLE["ink_muted"], fontsize=9)


def prepare_axes(ax) -> None:
    ax.set_facecolor(CHART_STYLE["surface"])
    ax.grid(True, color=CHART_STYLE["gridline"], linewidth=0.8, zorder=0)
    ax.set_axisbelow(True)
    for spine_name, spine in ax.spines.items():
        if spine_name in ("top", "right"):
            spine.set_visible(False)
        else:
            spine.set_color(CHART_STYLE["baseline"])
    ax.tick_params(colors=CHART_STYLE["ink_muted"])
    ax.xaxis.label.set_color(CHART_STYLE["ink_secondary"])
    ax.yaxis.label.set_color(CHART_STYLE["ink_secondary"])


# Per-frame Ethernet overhead that the reported frame length does not contain. An L2 length
# already contains the CRC, so the preamble with SFD (8 B) and the minimum interframe gap
# (12 B) remain. An L1 length contains the whole wire slot, so nothing remains. The
# theoretical line-rate limit is computed from this overhead (see gls_mod.py's rate_layer).
ETH_OVERHEAD_BYTES = {1: 0, 2: 20}


def theoretical_line_rate_bps(length_bytes: "np.ndarray", eth_rate_gbps: float,
                              rate_layer: int) -> "np.ndarray":
    """Bits/s reachable on a link of the given rate, once the per-frame overhead is
    subtracted. A measured curve can come close to this value, but never above it."""
    return eth_rate_gbps * 1e9 * length_bytes / (length_bytes + ETH_OVERHEAD_BYTES[rate_layer])


def plot_line_rate_limit(ax, x_min: float, x_max: float, eth_rate: object,
                         rate_layer: object, metric: Metric) -> None:
    """Draw the theoretical line-rate limit of this metric, if an Ethernet rate is known."""
    if eth_rate in (None, "") or x_max < x_min:
        return
    x = np.linspace(x_min, x_max, 200) if x_max > x_min else np.array([float(x_min)])
    bps = theoretical_line_rate_bps(x, float(eth_rate), int(rate_layer))
    ax.plot(x, metric.from_bps(bps, x) / metric.scale,
            color=CHART_STYLE["ink_muted"], linewidth=1, linestyle="--",
            marker=point_marker(len(x)), markersize=5,
            label=f"{eth_rate}G line-rate limit (L{rate_layer})", zorder=1)


def format_config_subtitle(config: Mapping[str, object]) -> str:
    """A small, muted one-line summary of the run configuration for the chart subtitle.

    Accepts either RunParams.chart_config() (values as ints/None) or the metadata read
    back from a results CSV (the same keys, but every value a string). The typing is
    loose and the "unset" values are handled for that reason.
    """
    def value_or(key: str, fallback: str) -> object:
        value = config.get(key)
        return value if value not in (None, "") else fallback

    parts = [
        f"channels: {value_or('channels', 'all')}",
        f"cycles: {config.get('cycles')}",
        f"freq: {float(config['frequency']) / 1e6:.0f} MHz",
        f"layer: L{config.get('rate_layer')}",
        f"buffers: count={value_or('buffer_count', 'default')}, "
        f"size={value_or('buffer_size', 'default')}",
    ]
    eth_rate = config.get("eth_rate")
    if eth_rate not in (None, ""):
        parts.append(f"eth rate: {eth_rate}G")
    return "   ".join(parts)


def new_panel_grid() -> Tuple[object, List[Tuple[str, str, Metric, object]]]:
    """Create the standard panel grid: RX DMA on the left, TX DMA on the right, one row
    per metric (Gbps on top, Mpps below).

    Returns the figure plus, for each panel, the results column it draws, its title,
    its metric and its axes - so both plotting functions below lay out their charts
    identically.
    """
    fig, axes = plt.subplots(len(METRICS), len(DIRECTIONS), figsize=(14, 10),
                             facecolor=CHART_STYLE["surface"], squeeze=False)
    panels = []
    for row, metric in enumerate(METRICS):
        for col, (direction, direction_title) in enumerate(DIRECTIONS):
            panels.append((f"{direction}_{metric.key}",
                           f"{direction_title} {metric.panel_title}",
                           metric, axes[row][col]))
    return fig, panels


def save_figure(fig, title: str, subtitle: str, out_path: Path) -> None:
    """Add the title and the muted run-configuration subtitle, then write the PNG."""
    fig.suptitle(title, color=CHART_STYLE["ink_primary"], fontsize=13, y=0.985)
    fig.text(0.5, 0.958, subtitle, ha="center", va="top", fontsize=8, color=CHART_STYLE["ink_muted"])
    fig.tight_layout(rect=(0, 0, 1, 0.94))
    fig.savefig(out_path, dpi=150, facecolor=fig.get_facecolor())
    plt.close(fig)


def plot_run(df: "pd.DataFrame", meta: FwMetadata, params: RunParams, out_path: Path) -> None:
    """Plot a single run: one curve per measured DMA mode, RX and TX side by side."""
    fig, panels = new_panel_grid()
    x_min, x_max = df["length"].min(), df["length"].max()

    for column, title, metric, ax in panels:
        prepare_axes(ax)
        plot_line_rate_limit(ax, x_min, x_max, params.eth_rate, params.rate_layer, metric)
        for mode in DMA_MODES:
            mode_rows = df[df["mode"] == mode]
            if mode_rows.empty or not has_data(mode_rows[column]):
                continue
            ax.plot(
                mode_rows["length"], mode_rows[column] / metric.scale,
                color=MODE_COLORS[mode], linewidth=2, label=MODE_LABELS[mode],
                marker=point_marker(len(mode_rows)), markersize=6,
            )
        finish_axes(ax, title, metric)

    save_figure(fig, f"DMA throughput sweep — {meta.label}",
                format_config_subtitle(params.chart_config()), out_path)


def cmd_run(args: argparse.Namespace) -> None:
    """Sweep every selected mode on the currently loaded FW, then save CSV and plots."""
    gls_mod_path = Path(__file__).parent / "gls_mod.py"
    if not gls_mod_path.exists():
        sys.exit(f"ERROR: gls_mod.py not found next to this script ({gls_mod_path})")

    modes = args.modes.split(",") if args.modes else DMA_MODES
    for m in modes:
        if m not in DMA_MODES:
            sys.exit(f"ERROR: unknown mode '{m}', expected one of: {', '.join(DMA_MODES)}")

    device = args.device or default_device_path()

    size_min, size_max, size_step = parse_frame_size(args.frame_size)

    params = RunParams(
        device=device,
        modes=modes,
        size_min=size_min,
        size_max=size_max,
        size_step=size_step,
        channels=args.channels,
        index=args.index,
        cycles=args.cycles,
        frequency=args.frequency,
        rate_layer=args.rate_layer,
        ext_loop=args.ext_loop,
        buffer_count=args.buffer_count,
        buffer_size=args.buffer_size,
        eth_rate=args.eth_rate,
    )
    if params.size_step < 1 or not (64 <= params.size_min <= params.size_max <= 1518):
        sys.exit(f"ERROR: invalid frame size sweep '{params.size_min} {params.size_max} "
                 f"{params.size_step}' — expected 64 <= MIN <= MAX <= 1518 and STEP >= 1")

    points_per_mode = (params.size_max - params.size_min) // params.size_step + 1
    print(f"Frame sizes: {params.size_min}-{params.size_max} step {params.size_step} "
          f"({points_per_mode} points per mode, {len(modes)} modes)")
    print("This can take a while, roughly 1.5-2 s per point per mode.")

    meta = read_fw_metadata(device)
    if not meta.build_revision and not args.fw_label:
        print("WARNING: no 'build-revision' found in the Device Tree — results will be "
              "tagged by build time instead. FW-to-FW comparisons are less reliable "
              "without a build revision; consider passing --fw-label explicitly.")
    if args.fw_label:
        meta.label_override = args.fw_label
    print(f"\nDetected FW: {meta.label}  (fw_id: {meta.fw_id})")

    if params.buffer_count is not None or params.buffer_size is not None:
        configure_dma_buffers(device, params.buffer_count, params.buffer_size)

    run_dir = Path(args.outdir) / meta.fw_id
    raw_dir = run_dir / "raw"

    frames = []
    try:
        for mode in modes:
            csv_path = run_gls_mode(gls_mod_path, mode, params, raw_dir / mode)
            frames.append(load_mode_report(csv_path, mode))
    except KeyboardInterrupt:
        sys.exit("\nInterrupted, partial results (if any) were not saved.")

    df = pd.concat(frames, ignore_index=True)
    if df.empty:
        sys.exit("ERROR: no data points were produced by any mode — check the frame size sweep.")

    results_csv = run_dir / f"results_{meta.fw_id}.csv"
    write_results_csv(df, meta, params, results_csv)
    print(f"\nSaved consolidated results: {results_csv}")

    if not args.skip_plots:
        plot_path = run_dir / f"throughput_{meta.fw_id}.png"
        plot_run(df, meta, params, plot_path)
        print(f"Saved plot: {plot_path}")

    print(f"\nDone. To compare against another FW build, run this again with a different "
          f"FW loaded, then:\n  {Path(sys.argv[0]).name} compare {run_dir} <other_run_dir>")


# ==============================================================================
# "compare" subcommand: overlay multiple runs produced by "run"
# ==============================================================================

COMPARABILITY_KEYS = ["card_name", "hostname", "size_min", "size_max", "size_step",
                      "channels", "cycles", "frequency", "rate_layer",
                      "buffer_count", "buffer_size", "eth_rate"]


def resolve_results_csv(path_arg: str) -> Path:
    """Accept either a results CSV or the run directory holding exactly one."""
    path = Path(path_arg)
    if path.is_file():
        return path
    matches = list(path.glob("results_*.csv"))
    if len(matches) == 1:
        return matches[0]
    sys.exit(f"ERROR: could not find a unique results_*.csv under '{path}' "
             f"(found {len(matches)})")


def check_comparability(all_meta: List[Dict[str, str]], labels: List[str]) -> None:
    """Warn about settings that differ between runs, since throughput is only
    comparable across FW builds when the card, host and sweep settings all match."""
    for key in COMPARABILITY_KEYS:
        values = {m.get(key, "") for m in all_meta}
        if len(values) > 1:
            detail = ", ".join(f"{lbl}={m.get(key, '?')}" for lbl, m in zip(labels, all_meta))
            print(f"WARNING: runs differ in '{key}' — results may not be directly comparable ({detail})")


def plot_compare(runs: List[Tuple[str, "pd.DataFrame"]], mode: str,
                 meta: Dict[str, str], out_path: Path) -> None:
    """meta is one run's metadata, normally the first one. It is used only for the config
    subtitle and for the line-rate limit. check_comparability() already warns when the compared
    runs differ in the fields that matter for those, see COMPARABILITY_KEYS."""
    fig, panels = new_panel_grid()
    all_lengths = pd.concat([df[df["mode"] == mode]["length"] for _, df in runs])
    x_min, x_max = (all_lengths.min(), all_lengths.max()) if not all_lengths.empty else (0, -1)

    for column, title, metric, ax in panels:
        prepare_axes(ax)
        plot_line_rate_limit(ax, x_min, x_max, meta.get("eth_rate"),
                             meta.get("rate_layer") or 2, metric)
        for run_index, (label, df) in enumerate(runs):
            mode_rows = df[df["mode"] == mode]
            if mode_rows.empty or not has_data(mode_rows[column]):
                continue
            color = CATEGORICAL_PALETTE[run_index % len(CATEGORICAL_PALETTE)]
            ax.plot(mode_rows["length"], mode_rows[column] / metric.scale,
                    color=color, linewidth=2, label=label,
                    marker=point_marker(len(mode_rows)), markersize=6)
        finish_axes(ax, title, metric)

    save_figure(fig, f"DMA throughput comparison — {MODE_LABELS[mode]}",
                format_config_subtitle(meta), out_path)


def cmd_compare(args: argparse.Namespace) -> None:
    """Overlay previously saved runs, one chart per DMA mode."""
    if len(args.runs) < 2:
        sys.exit("ERROR: 'compare' needs at least two run directories/CSV files")

    csv_paths = [resolve_results_csv(r) for r in args.runs]
    loaded = [read_results_csv(p) for p in csv_paths]
    all_meta = [m for _, m in loaded]

    if args.labels:
        labels = args.labels.split(",")
        if len(labels) != len(csv_paths):
            sys.exit(f"ERROR: --labels needs exactly {len(csv_paths)} comma-separated entries")
    else:
        # "label" already includes the FW build identity (project/variant/revision or,
        # if --fw-label was used for the run, that override) — see FwMetadata.label().
        labels = [m.get("label") or m.get("project_name") or m.get("card_name") or p.stem
                  for p, (_, m) in zip(csv_paths, loaded)]

    if len(set(labels)) != len(labels):
        print(f"WARNING: run labels are not unique ({labels}) — the comparison chart legend "
              f"will be ambiguous; pass --labels to disambiguate.")

    print("Comparing runs:")
    for label, path in zip(labels, csv_paths):
        print(f"  - {label}: {path}")
    check_comparability(all_meta, labels)

    runs = list(zip(labels, (df for df, _ in loaded)))
    modes_by_run = [set(df["mode"].unique()) for _, df in runs]
    modes_present = sorted(
        set.union(*modes_by_run),
        key=lambda m: DMA_MODES.index(m) if m in DMA_MODES else len(DMA_MODES),
    )
    for mode in modes_present:
        missing = [label for (label, _), present in zip(runs, modes_by_run) if mode not in present]
        if missing:
            print(f"WARNING: mode '{mode}' is missing from run(s): {', '.join(missing)} "
                  f"— its comparison chart will only show the other run(s)")

    outdir = Path(args.outdir) if args.outdir else Path("dma_throughput_results") / "compare"
    outdir.mkdir(parents=True, exist_ok=True)
    for mode in modes_present:
        out_path = outdir / f"compare_{mode}.png"
        plot_compare(runs, mode, all_meta[0], out_path)
        print(f"Saved plot: {out_path}")


# ==============================================================================
# CLI
# ==============================================================================

def main() -> None:
    desc = (
        "Automates DMA throughput sweeps using gls_mod.py across the four DMA scenarios\n"
        "(RX DMA only, TX DMA only, RX+TX DMA independent, RX+TX DMA via SW loopback)\n"
        "for a range of frame lengths, then plots the results. Every chart shows the bit\n"
        "rate in Gbps and the frame rate in Mpps. Each run is tagged with the FW build\n"
        "identity so results from different FW versions can be compared."
    )
    parser = argparse.ArgumentParser(
        prog="dma_throughput_sweep.py",
        description=desc,
        formatter_class=argparse.RawTextHelpFormatter,
    )
    sub = parser.add_subparsers(dest="command", required=True)

    p_run = sub.add_parser("run", help="perform a throughput sweep for the current FW")
    p_run.add_argument("-d", "--device", default=None,
                       help="target device; default: the nfb library default (usually /dev/nfb0)")
    p_run.add_argument("-m", "--modes", default=None,
                       help="comma-separated subset of modes to run: " + ",".join(DMA_MODES) +
                             "; default: all four")
    p_run.add_argument("-s", "--frame_size", nargs="+", type=int, metavar="N",
                       default=[64, 1518, 4],
                       help="frame size sweep in bytes as 'MIN MAX STEP', or a single frame\n"
                            "length to measure just that one size; default: 64 1518 4")
    p_run.add_argument("-c", "--channels", help="DMA channel range 'min-max'; default: all available")
    p_run.add_argument("-i", "--index", help="GLS instance index/indexes; default: gls_mod.py default (0)")
    p_run.add_argument("-C", "--cycles", type=int, default=4, help="measurement cycles averaged per size; default: 4")
    p_run.add_argument("-f", "--frequency", type=int, default=200_000_000, help="APP core clock [Hz]; default: 200e6")
    p_run.add_argument("-r", "--rate_layer", type=int, default=2, choices=[1, 2], help="ISO/OSI layer 1 or 2; default: 2")
    p_run.add_argument("-e", "--ext_loop", action="store_true", help="force external loopback (passed through to gls_mod.py)")
    p_run.add_argument("--buffer-count", type=int, default=None,
                       help="set the kernel DMA buffer count via 'nfb-dma -C' before the sweep\n"
                            "(DMA Medusa only). Requires sudo. The setting is global for the\n"
                            "device and stays set after this script exits; default: unchanged")
    p_run.add_argument("--buffer-size", type=int, default=None,
                       help="set the kernel DMA buffer size via 'nfb-dma -B' before the sweep\n"
                            "(DMA Medusa only). Requires sudo. The setting is global for the\n"
                            "device and stays set after this script exits; default: unchanged.\n"
                            "For MTU/jumbo-sized packets (roughly 4096 B and up) the default is\n"
                            "usually too small for a whole packet in a single DMA descriptor")
    p_run.add_argument("--eth-rate", type=int, default=None, metavar="GBPS",
                       help="physical Ethernet line rate in Gbps (e.g. 100 or 400). If set, every\n"
                            "chart shows the theoretical throughput limit for this rate;\n"
                            "default: none, no limit curve")
    p_run.add_argument("--fw-label", help="override the auto-detected FW label/id (use if the Device Tree has no build-revision)")
    p_run.add_argument("-o", "--outdir", default="dma_throughput_results", help="output directory; default: ./dma_throughput_results")
    p_run.add_argument("--skip-plots", action="store_true", help="only produce the consolidated CSV, no PNG plots")
    p_run.set_defaults(func=cmd_run)

    p_cmp = sub.add_parser("compare", help="overlay two or more previous 'run' results")
    p_cmp.add_argument("runs", nargs="+", help="two or more run output directories (or results_*.csv files) produced by 'run'")
    p_cmp.add_argument("--labels", help="comma-separated legend labels, one per run (default: derived from FW metadata)")
    p_cmp.add_argument("-o", "--outdir", default=None, help="output directory for comparison plots; default: ./dma_throughput_results/compare")
    p_cmp.set_defaults(func=cmd_compare)

    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
