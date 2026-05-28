---
name: ndk-cocotb-ver
description: Design and implementation of cocotb verifications in NDK platform - general principles, MI bus, integration with Python/C tools via Device Tree and libnfb API.
---

# NDK Cocotb Verification

This skill provides a general guide for creating verification tests using the cocotb framework in the NDK-FPGA platform, with emphasis on modular structure, MI bus, and integration with external tools.

## When to Use This Skill

- You need to create a new cocotb test for a VHDL component in NDK-FPGA
- You're looking for general principles and patterns for cocotb verifications
- You need to integrate a test with Python/C tools via Device Tree and libnfb API
- You're working with MI (Memory Interface) bus
- You want to understand modular test structure

## General Principles of Cocotb Verifications in NDK

### 1. Simplicity and Clarity

**Keep verifications as simple and clear as possible.** Avoid unnecessarily complicated constructions. The test code should be easy to read, understand, and maintain. Prefer straightforward solutions over clever but obscure ones.

### 2. Modular Test Structure

Recommended structure for clarity and reusability:

```
component_name/
├── cocotb/
│   ├── cocotb_test.py      # Test definitions (@cocotb.test())
│   ├── testbench.py        # Testbench infrastructure
│   ├── model.py            # Reference model (expectation calculation)
│   ├── scoreboard.py       # Dataclass + compare function
│   ├── monitor.py          # (Optional) Custom monitors
│   ├── Makefile            # Build configuration
│   ├── pyproject.toml      # Python dependencies
│   └── cocotb_test_sig.fdo # Signals for waveform viewer
```

**Benefits**:
- Better code organization
- Component reusability (model, monitor)
- Easier CI checking (smaller files)
- Clearer type annotations

> **Note:** For simpler tests, model and scoreboard may be kept inline in `testbench.py`. Very compact tests (e.g. `frame_fracturer`) can even define the `testbench` class directly in `cocotb_test.py`. The agent should ask the user which approach they prefer for their specific case before proceeding.

### 3. One Generic Randomized Test

Start with **one generic randomized test** that covers various scenarios through parameterization. See [`comp/axis_tools/edit/head_trimmer/cocotb/cocotb_test.py`](comp/axis_tools/edit/head_trimmer/cocotb/cocotb_test.py:41) for a well-structured example.

#### Backpressure Patterns

Use the shared utilities from [`cocotbext.ofm.ver.backpressure`](python/cocotbext/cocotbext/ofm/ver/backpressure.py).

```python
from cocotbext.ofm.ver.backpressure import BackpressureConfig, apply_backpressure

tx_task = cocotb.start_soon(
    apply_backpressure(dut.TX_AXI_TREADY, dut.CLK, BackpressureConfig(1, 5, 0.5))
)
```

For tests that already use `BitDriver`, a compatible generator is also available:

```python
from cocotb_bus.drivers import BitDriver
from cocotbext.ofm.ver.backpressure import BackpressureGenerator, BackpressureConfig

bp = BitDriver(dut.TX_DST_RDY, dut.CLK)
bp.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))
```

**Used in**: [`comp/axis_tools/edit/head_trimmer/cocotb/cocotb_test.py`](comp/axis_tools/edit/head_trimmer/cocotb/cocotb_test.py:29), [`comp/axis_tools/edit/packet_concatenator/cocotb/cocotb_test.py`](comp/axis_tools/edit/packet_concatenator/cocotb/cocotb_test.py)

#### Rate Limiter Configurations

```python
from cocotbext.ofm.base.generators import ItemRateLimiter, EthernetRateLimiter

# Item-based rate limiting (percentage of max throughput)
tb.stream_in.set_idle_generator(
    ItemRateLimiter(rate_percentage=70.0, max_idles=5, zero_idles_chance=50)
)

# Ethernet-specific rate limiting (bitrate in Mbps)
tb.stream_in.set_idle_generator(
    EthernetRateLimiter(bitrate=1000.0)  # 1000 Mbps = 1 Gbps
)

# Common configurations:
# - Normal traffic: ItemRateLimiter(rate_percentage=70-80, max_idles=5)
# - High throughput: ItemRateLimiter(rate_percentage=90-95, max_idles=2)
# - Bursty traffic: ItemRateLimiter(rate_percentage=50, max_idles=20, zero_idles_chance=80)
# - 1 Gbps Ethernet: EthernetRateLimiter(bitrate=1000.0)
# - 10 Gbps Ethernet: EthernetRateLimiter(bitrate=10000.0)
```

**Used in**: [`comp/axis_tools/edit/head_trimmer/cocotb/cocotb_test.py`](comp/axis_tools/edit/head_trimmer/cocotb/cocotb_test.py:58), [`comp/mfb_tools/storage/fifox/cocotb/cocotb_test.py`](comp/mfb_tools/storage/fifox/cocotb/cocotb_test.py)

**Benefits of this approach**:
- One maintainable test instead of many duplicates
- Different scenarios via parameterization
- Easy to add new variants
- Coverage of various corner cases

**However**, supplement the generic test with **specific tests for risky situations**:

- Edge cases (minimum/maximum values, boundary conditions)
- Known bug regression tests
- Critical functionality that must be explicitly verified
- Corner cases that randomization might not hit reliably

> **Alternative:** For compact tests, parameters can be set as default arguments directly in `@cocotb.test()` without a separate generic wrapper.

### 4. Integration with Python/C Tools via Device Tree

NDK-FPGA enables integration of cocotb tests with external Python/C tools via **Device Tree** and **libnfb API**. For detailed documentation, see [`doc/source/cocotbext.rst`](doc/source/cocotbext.rst).

#### Device Tree in Simulation

For component-level verification, use [`Servicer`](python/cocotbext/cocotbext/ofm/utils/servicer.py) with Device Tree Blob (DTB). For small simulations, use [`MIDriver`](python/cocotbext/cocotbext/ofm/mi/driver.py) instead of `NFBDevice` which is intended for top-level simulations:

```python
# testbench.py
import cocotb
from cocotbext.ofm.mi.driver import MIDriver
from cocotbext.ofm.utils.servicer import Servicer
from cocotbext.ofm.utils.device import create_dtb_simple
import nfb
from typing import Any

class Testbench:
    _REG0_OFFSET: int = 0x0
    _REG1_OFFSET: int = 0x4

    def __init__(self, dut: Any) -> None:
        self.dut = dut
        self.mi_drv = MIDriver(dut, "MI", dut.CLK)
        dtb = create_dtb_simple(
            comp_name="TEST_COMPONENT",
            comp_base=0,
            comp_size=0x1000,
            compatible_str="cesnet,ndk,test"
        )
        self.servicer = Servicer(device=self.mi_drv, dtb=dtb)

    async def config_example(self) -> None:
        """Read and write registers via Device Tree using MI driver."""
        dev = await cocotb.external(nfb.open)(self.servicer.path())

        await dev.write32(self._REG1_OFFSET, 0x42)
```

**Used in**: [`comp/mvb_tools/storage/mvb_hash_table_simple/cocotb/cocotb_test.py`](comp/mvb_tools/storage/mvb_hash_table_simple/cocotb/cocotb_test.py:223)

### 5. Working with MI (Memory Interface) Bus

For MI bus specifications and characteristics, see [`doc/source/mi.rst`](doc/source/mi.rst).

For component-level verification, use the MI drivers and monitors from [`cocotbext.ofm.mi`](python/cocotbext/cocotbext/ofm/mi/):

| Type | Classes |
|------|---------|
| **Request Driver** | [`MIRequestDriver`](python/cocotbext/cocotbext/ofm/mi/drivers.py), [`MIRequestDriverAgent`](python/cocotbext/cocotbext/ofm/mi/drivers.py) |
| **Response Driver** | [`MIResponseDriver`](python/cocotbext/cocotbext/ofm/mi/drivers.py), [`MIResponseDriverAgent`](python/cocotbext/cocotbext/ofm/mi/drivers.py) |
| **Monitor** | [`MIMonitor`](python/cocotbext/cocotbext/ofm/mi/monitors.py) |
| **Proxy Monitor** | [`MIProxyMonitor`](python/cocotbext/cocotbext/ofm/mi/proxymonitor.py) |
| **Transactions** | [`MiRequestTransaction`](python/cocotbext/cocotbext/ofm/mi/transaction.py), [`MiResponseTransaction`](python/cocotbext/cocotbext/ofm/mi/transaction.py) |

**Used in**: [`comp/mi_tools/pipe/cocotb/cocotb_test.py`](comp/mi_tools/pipe/cocotb/cocotb_test.py), [`comp/mi_tools/test_space/cocotb/cocotb_test.py`](comp/mi_tools/test_space/cocotb/cocotb_test.py)

### 6. Available Drivers by Bus

| Bus | Drivers | Reference Implementation |
|-----|---------|-------------------------|
| **MFB** | `MFBDriver`, `MFBMonitor` | [`comp/mfb_tools/storage/fifox/cocotb/`](comp/mfb_tools/storage/fifox/cocotb/) |
| **MVB** | `MVBDriver`, `MVBMonitor` | [`comp/mvb_tools/storage/fifox/cocotb/`](comp/mvb_tools/storage/fifox/cocotb/) |
| **AXI4-Stream** | `Axi4StreamMaster`, `Axi4Stream` | [`comp/axis_tools/edit/packet_editor/cocotb/`](comp/axis_tools/edit/packet_editor/cocotb/) |
| **MI** | [`MIRequestDriver`](python/cocotbext/cocotbext/ofm/mi/drivers.py), [`MIMonitor`](python/cocotbext/cocotbext/ofm/mi/monitors.py) | [`comp/mi_tools/pipe/cocotb/`](comp/mi_tools/pipe/cocotb/) |

For detailed bus documentation, see [`doc/source/mfb.rst`](doc/source/mfb.rst), [`doc/source/mvb.rst`](doc/source/mvb.rst), [`doc/source/axi.rst`](doc/source/axi.rst).

### 7. Running Simulations

#### NVC Simulator (Recommended - Open Source)

```bash
cd comp/your_component/cocotb/
make cocotb-venv
source venv-*/bin/activate
make TARGET=nvc-sim

# With debug logging
export COCOTB_LOG_LEVEL=DEBUG
make TARGET=nvc-sim
```

**Note on Device Family:** Some designs use encrypted IP models (e.g., DSP counters) that are not available for NVC simulation. If you encounter issues with the default `AGILEX` device, try using `ULTRASCALE` instead:

#### QuestaSim (Advanced Analysis)

```bash
make SIM_FLAGS=-c  # CLI mode (no GUI)
```

### 8. Debug Patterns

#### Comments Guidelines

**Write only comments that explain WHY, not WHAT.** Good code should be mostly self-explanatory.

**Rules:**
1. Comment explains **why** something is done (non-obvious reasoning)
2. Comment explains **workarounds** for edge cases or bugs
3. Don't comment what the code does - if code complexity allows, rewrite to be clearer; otherwise explain the function of complex parts
4. Don't add comments that just translate code to English

#### Long Transaction Hex Dump

Use [`format_bytes()`](python/cocotbext/cocotbext/ofm/utils/hex_formatter.py) from `cocotbext.ofm.utils.hex_formatter`:

```python
from cocotbext.ofm.utils.hex_formatter import format_bytes, format_hex_short

# Full hex dump with two-level grouping (default: 16 bytes/line, space between bytes, double space every 4 bytes)
format_bytes(transaction.TDATA, label="TDATA")

# Compact single-line hex
format_hex_short(packet, max_bytes=32, label="HDR")
```

**Used in**: [`python/cocotbext/cocotbext/ofm/axi4stream/transaction.py`](python/cocotbext/cocotbext/ofm/axi4stream/transaction.py), [`python/cocotbext/cocotbext/ofm/mfb/transaction.py`](python/cocotbext/cocotbext/ofm/mfb/transaction.py)

**Tip**: For complex verifications, include parsed metadata alongside raw hex data:

```python
# Example from eth_parser scoreboard - show both raw hex and parsed headers
msg += f"\nExpected packet:\n{format_bytes(expected.packet_bytes, label='Raw data')}"
msg += f"\nParsed headers: ETH(src={expected.src_mac}, dst={expected.dst_mac})"
msg += f" IPv4(src={expected.src_ip}, dst={expected.dst_ip})"
```

**Examples**: [`comp/axis_tools/logic/eth_parser/cocotb/scoreboard.py`](comp/axis_tools/logic/eth_parser/cocotb/scoreboard.py), [`comp/mfb_tools/logic/checksum_l3l4/cocotb/scoreboard.py`](comp/mfb_tools/logic/checksum_l3l4/cocotb/scoreboard.py)

#### Structured Data Comparison

```python
from dataclasses import dataclass

@dataclass
class Result:
    """Structured data comparison result."""
    field_a: int = 0
    field_b: int = 0

def compare(expected: Result, actual: Result) -> tuple[bool, str]:
    """Compare two Result instances and return formatted diff."""
    rows = [f"# {'Field':<18} {'Expected':>14} {'Actual':>14}"]
    has_error = False
    for field in fields(expected):
        e, a = getattr(expected, field.name), getattr(actual, field.name)
        match = " " if e == a else "X"
        has_error |= match == "X"
        rows.append(f"# {match} {field.name:<18} {e:>14} {a:>14}")
    return not has_error, "\n".join(rows)
```

**Used in**: [`comp/axis_tools/logic/eth_parser/cocotb/scoreboard.py`](comp/axis_tools/logic/eth_parser/cocotb/scoreboard.py)

#### Parsing MVB Sub-fields

```python
from dataclasses import dataclass
from cocotbext.ofm.mvb.transaction import MvbTrClassic

@dataclass
class MvbMetadata:
    """Typed MVB metadata structure."""
    src_port: int = 0
    dst_port: int = 0
    flags: int = 0
    priority: int = 0

def parse_mvb_meta(tr: MvbTrClassic) -> MvbMetadata:
    """Parse MVB metadata from transaction data word."""
    d = tr.data
    return MvbMetadata(
        src_port=(d >> 0)  & 0xFF,
        dst_port=(d >> 8)  & 0xFF,
        flags=   (d >> 16) & 0x0F,
        priority=(d >> 20) & 0x07,
    )
```

**Used in**: [`comp/mvb_tools/storage/fifox/cocotb/cocotb_test.py`](comp/mvb_tools/storage/fifox/cocotb/cocotb_test.py)

### 9. Best Practices

1. **One generic test** with parameterization, supplemented by specific tests for risky situations
2. **Modular structure** - testbench, model, scoreboard separate
3. **Type annotations** for all functions and variables
4. **Randomization** - various packet lengths, backpressure, rate limiters
5. **Device Tree integration** for collaboration with Python/C tools
6. **Code quality** - run `tests/ci/pycodestyle.sh` after every code change
7. **Reference implementation** - use existing tests as examples

### 10. Reference Implementations

| Topic | Path |
|-------|------|
| **Modular structure** | [`comp/axis_tools/edit/packet_editor/cocotb/`](comp/axis_tools/edit/packet_editor/cocotb/) |
| **Randomized test** | [`comp/axis_tools/edit/head_trimmer/cocotb/cocotb_test.py`](comp/axis_tools/edit/head_trimmer/cocotb/cocotb_test.py) |
| **Device Tree + Servicer** | [`comp/mvb_tools/storage/mvb_hash_table_simple/cocotb/cocotb_test.py`](comp/mvb_tools/storage/mvb_hash_table_simple/cocotb/cocotb_test.py) |
| **MI verification** | [`comp/mi_tools/pipe/cocotb/`](comp/mi_tools/pipe/cocotb/) |
| **Custom monitors** | [`comp/axis_tools/logic/eth_parser/cocotb/monitor.py`](comp/axis_tools/logic/eth_parser/cocotb/monitor.py) |
| **Custom drivers** | [`comp/axis_tools/flow/frame_fracturer/cocotb/axi4s_frfr_driver.py`](comp/axis_tools/flow/frame_fracturer/cocotb/axi4s_frfr_driver.py) |

### 11. Additional Documentation

- **Cocotb basics**: [`doc/source/basic_cocotb_test.rst`](doc/source/basic_cocotb_test.rst)
- **Cocotbext-NDK detailed**: [`doc/source/cocotbext.rst`](doc/source/cocotbext.rst)
- **Tips & Tricks**: [`doc/source/cocotb_tips_and_tricks.rst`](doc/source/cocotb_tips_and_tricks.rst)
- **Bus documentation**: [`doc/source/mi.rst`](doc/source/mi.rst), [`doc/source/mfb.rst`](doc/source/mfb.rst), [`doc/source/mvb.rst`](doc/source/mvb.rst), [`doc/source/axi.rst`](doc/source/axi.rst)
