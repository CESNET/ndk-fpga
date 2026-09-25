# NDK-FPGA

[![GitHub release](https://img.shields.io/github/v/release/CESNET/ndk-fpga)](https://github.com/CESNET/ndk-fpga/releases)
[![Docs build](https://github.com/CESNET/ndk-fpga/actions/workflows/doc.yml/badge.svg)](https://github.com/CESNET/ndk-fpga/actions/workflows/doc.yml)
[![docs: release](https://img.shields.io/badge/docs-release-blue)](https://cesnet.github.io/ndk-fpga/release/)
[![docs: devel](https://img.shields.io/badge/docs-devel-blue)](https://cesnet.github.io/ndk-fpga/devel/)
[![License](https://img.shields.io/github/license/CESNET/ndk-fpga)](LICENSE)

This repository contains FPGA part of the Network Development Kit (NDK) for FPGA acceleration cards. The NDK allows users to quickly and easily develop FPGA-accelerated network applications. The NDK is optimized for high throughput and scalability: it scales from 10G to 400G Ethernet, depending on the target card (see the table below). The NDK-based Minimal (reference) application is also included in this (NDK-FPGA) repository.

The NDK-based Minimal application is a simple example of how to build an FPGA application using the NDK. It can also be a starting point for your NDK-based application. The NDK-based Minimal application does not process network packets in any way; it only sends and receives them. If the DMA IP is enabled, then it forwards the network packets to the computer memory. You can find more detailed information in [the NDK-FPGA documentation (devel branch) here](https://cesnet.github.io/ndk-fpga/devel/).

**Please note that some integrated IP (e.g. DMA Medusa IP) are not part of the open-source NDK-FPGA. These IPs can only be obtained through our partners, [see the section Partners](#partners).**

## How to start

Before you get started, there are a few requirements that you need to have.

### Requirements and supported FPGA cards

- To build the FPGA firmware, you must have installed the **Intel Quartus Prime Pro 25.1** or the **Xilinx Vivado 2025.1** tool, depending on the target card (see the table below), including a valid license.
- To run HDL verifications, we recommend using the **Questa Sim-64 2025.2** tool. Verification is based on UVM and [cocotb](https://www.cocotb.org/) (Python); Questa is the default simulator for both.
- To control an FPGA card with an application based on the NDK framework, you also need:
    - [NDK Linux driver and SW tools](https://github.com/CESNET/ndk-sw). We recommend using the latest version; we try to maintain backward compatibility between the NDK-FPGA and NDK-SW versions, but it is not 100% guaranteed.
- Supported FPGA cards in the NDK framework available as open-source:

| FPGA card | Required tool | Ethernet (max) | PCIe (max) |
| --- | --- | --- | --- |
| ReflexCES XpressSX AGI-FH400G [1] | Quartus Prime Pro | 1x 400G | Gen5 x16 |
| Intel Stratix 10 DX FPGA Development Kit [2] | Quartus Prime Pro | 2x 100G | Gen4 x16 |
| Silicom fb4CGg3@VU9P [3] | Vivado | 4x 100G | Gen3 x16 |
| Silicom fb2CGhh@KU15P | Vivado | 2x 100G | Gen3 x16 |
| Silicom fb2CDg1@AGM39D-2 [4] | Quartus Prime Pro | 2x 400G | Gen5 x16 |
| Silicom N5014 | Quartus Prime Pro | 4x 100G | Gen4 x16 |
| Silicom N6010 | Quartus Prime Pro | 2x 100G | Gen4 x16 |
| BittWare IA-420f | Quartus Prime Pro | 2x 100G | Gen4 x16 |
| BittWare IA-440i | Quartus Prime Pro | 1x 400G | Gen5 x16 |
| BittWare IA-860m | Quartus Prime Pro | 2x 400G | Gen5 x16 |
| AMD/Xilinx Alveo U200 | Vivado | 2x 100G | Gen3 x16 |
| AMD/Xilinx Alveo U55C | Vivado | 2x 100G | Gen3 x16 |
| AMD/Xilinx VCU118 Evaluation Kit [5] | Vivado | 2x 100G | Gen3 x16 |
| PRO DESIGN FALCON Stratix 10 [6] | Quartus Prime Pro | 2x 100G | Gen3 x16 |
| Terasic Mercury A2700 Accelerator Card | Quartus Prime Pro | 1x 400G | Gen5 x16 |
| iWave G35P Accelerator card | Vivado | 2x 100G | Gen3 x16 |
| Napatech NT200A02 | Vivado | 2x 100G | Gen3 x16 |

Notes:

1. AGI-FH400G cards with BOARD_REV = 0 or 1 are an exception and require the older Quartus Prime Pro 22.4; newer board revisions use the current version stated above.
2. Product code DK-DEV-1SDX-P.
3. Also available in the fb2CGg3@VU9P variant with 2x 100G Ethernet.
4. Also known as ThunderFjord.
5. Full name: AMD/Xilinx Virtex UltraScale+ FPGA VCU118 Evaluation Kit.
6. EXPERIMENTAL support only.

The Ethernet and PCIe columns show the maximum configuration supported by the NDK firmware on the given card; lower speeds and other PCIe configurations are typically also available (see the readme of each card).

**Please note:** Support for the FPGA cards listed above is provided on a best-effort community basis; we do not have the capacity to regularly test all cards and all their possible configurations. If you need professional support or guaranteed maintenance, it can typically be arranged through our partners (see the [Partners](#partners) section).

### How to clone the necessary repositories

Just clone the NDK-FPGA repository from GitHub:

```
git clone https://github.com/CESNET/ndk-fpga.git
```

CESNET developers who have access to closed-source repositories can use a single command to clone the repository, including its submodules (from private GitLab):
```
git clone --recursive git@gitlab.liberouter.org:ndk/ndk-fpga.git
```

Note: The public GitHub repository does not use Git submodules; the `extra/` directory contains only integration points for closed-source IP (available to CESNET developers and partners). For a stable state of the repository, use a release tag or the `release` branch; active development takes place on the `devel` branch. See [CHANGELOG.md](CHANGELOG.md) for an overview of changes between releases.

### Quick start: build the firmware

To build the FPGA firmware of the Minimal application for your card, run:

```
make -C apps/minimal/build/<card>   # e.g. make -C apps/minimal/build/n6010
```

### Next steps

The [NDK-FPGA documentation (devel branch) in chapter "How to start"](https://cesnet.github.io/ndk-fpga/devel/ndk_core/doc/how_to_start.html) lists further steps for building the FPGA firmware, loading it into the FPGA card and also using it.

## Repository structure

- `comp/`: reusable VHDL components and IP (bus infrastructure, DMA, PCIe, NIC, ...), often with their own verifications
- `core/`: the NDK core (network/PCIe/DMA pipeline, MI address space and device tree), instantiated by every application
- `apps/minimal/`: the NDK-based Minimal (reference) application, including firmware build Makefiles and tests
- `cards/`: card-specific configuration, constraints and IP
- `build/`: shared Tcl/Make build system scripts
- `doc/`: sources of the Sphinx-based documentation
- `python/`: Python packages used by verifications and tools
- `extra/`: integration points for closed-source IP (private Git submodules)

## Documentation

We use a documentation system based on the [Sphinx tool](https://www.sphinx-doc.org), which compiles complete documentation from source files in the [reStructuredText](https://docutils.sourceforge.io/rst.html) format. We also use the [Sphinx-vhdl](https://github.com/CESNET/sphinx-vhdl) for generating documentation from the VHDL code. The documentation automatically builds with each contribution to the devel/release branch and is available online here:
- [**NDK-FPGA documentation (release branch)**](https://cesnet.github.io/ndk-fpga/release/)
- [**NDK-FPGA documentation (devel branch)**](https://cesnet.github.io/ndk-fpga/devel/)

### How to manually build documentation

First, you need to prepare the environment:
```
$ cd doc
$ python3 -m venv venv-doc
$ source venv-doc/bin/activate
$ pip install -r requirements.txt
```

Then the documentation is generated simply by issuing this command:
```
$ make html
```

The output is in the `doc/build/index.html` file.

## Reporting issues

- Issues in the FPGA firmware and this repository in general: use [GitHub Issues of NDK-FPGA](https://github.com/CESNET/ndk-fpga/issues).
- Issues with the Linux driver and SW tools: use [GitHub Issues of NDK-SW](https://github.com/CESNET/ndk-sw/issues).

For professional (paid) support, see the [Partners](#partners) section.

## Partners

### DYNANIC (formerly BrnoLogic)

The NDK including the DMA Medusa IP and professional support is [available through our partner DYNANIC](https://dyna-nic.com/ndk-and-dma-engine/).

## Related publications

- J. Cabal, J. Sikora, Š. Friedl, M. Špinler and J. Kořenek, "[FPL Demo: 400G FPGA Packet Capture Based on Network Development Kit](https://ieeexplore.ieee.org/document/10035175)," 2022 32nd International Conference on Field-Programmable Logic and Applications (FPL), Belfast, United Kingdom, 2022, pp. 474-474, doi: [10.1109/FPL57034.2022.00090](https://doi.org/10.1109/FPL57034.2022.00090).
- J. Kubálek, J. Cabal, M. Špinler and R. Iša, "[DMA Medusa: A Vendor-Independent FPGA-Based Architecture for 400 Gbps DMA Transfers](https://ieeexplore.ieee.org/document/9444087)," *2021 IEEE 29th Annual International Symposium on Field-Programmable Custom Computing Machines (FCCM)*, 2021, pp. 258-258, doi: [10.1109/FCCM51124.2021.00045](https://doi.org/10.1109/FCCM51124.2021.00045).
- L. Kekely, J. Cabal, V. Puš and J. Kořenek, "[Multi Buses: Theory and Practical Considerations of Data Bus Width Scaling in FPGAs](https://ieeexplore.ieee.org/document/9217811)," *2020 23rd Euromicro Conference on Digital System Design (DSD)*, 2020, pp. 49-56, doi: [10.1109/DSD51259.2020.00020](https://doi.org/10.1109/DSD51259.2020.00020).

## License

Unless otherwise noted, the content of this repository is available under the BSD 3-Clause License. Please read [LICENSE file](LICENSE).

- See also the license information (in README.md) in each Git submodule.

### Modules/files taken from other sources

- [I2C Master controller](comp/ctrls/i2c_hw/) by Richard Herveille from [opencores.org](https://opencores.org/projects/i2c) in `comp/ctrls/i2c_hw` under something like a BSD license.
- [SPI Master controller](comp/ctrls/spi/) by Jonny Doin from [opencores.org](https://opencores.org/projects/spi_master_slave) in `comp/ctrls/spi` under LGPL license.
- The .ip files located in the `/comp/base/misc/adc_sensors/` folder were generated in Intel Quartus Prime Pro, and their use may be subject to additional license agreements.
- The .ip file `comp/ctrls/sdm_client/mailbox_client.ip` was generated in Intel Quartus Prime Pro, and their use may be subject to additional license agreements.
- The .ip files located in the `cards/<VENDOR>/<CARD_NAME>/src/ip/` folder were generated in the Intel Quartus Prime Pro, and their use may be subject to additional license agreements.
- The .xci files located in the `cards/<VENDOR>/<CARD_NAME>/src/ip/` folder were generated in the Xilinx Vivado, and their use may be subject to additional license agreements.
- The files located in the `cards/silicom/n6010/src/comp/pmci/pmci_ip` and `cards/silicom/n6010/scripts` folders were taken from the [ofs-agx7-pcie-attach repository](https://github.com/OFS/ofs-agx7-pcie-attach) and are subject to the MIT license. Please read [LICENSE.txt file](cards/silicom/n6010/scripts/LICENSE.txt).
- The files located in the `cards/silicom/n5014/src/comp/hbm` folder were taken from the [ofs-fim-common repository](https://github.com/OFS/ofs-fim-common) and are subject to the MIT license. Please read [LICENSE.txt file](cards/silicom/n5014/src/comp/hbm/LICENSE.txt).
- The files located in the `comp/base/hash/spookyhash/sw/` by Bob Jenkins from [burtleburtle.net](https://burtleburtle.net/bob/hash/spooky.html), Public domain.

## Repository Maintainer

- Jakub Cabal, cabal@cesnet.cz

## Acknowledgment

This work was supported by the Ministry of Education, Youth and Sports of the Czech Republic through the e-INFRA CZ (ID:90254).
