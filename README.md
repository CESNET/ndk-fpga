# NDK-FPGA

This repository contains FPGA part of the Network Development Kit (NDK) for FPGA acceleration cards. The NDK allows users to quickly and easily develop FPGA-accelerated network applications. The NDK is optimized for high throughput and scalability to support up to 400 Gigabit Ethernet. The NDK-based Minimal (reference) application is also included in this (NDK-FPGA) repository.
 
The NDK-based Minimal application is a simple example of how to build an FPGA application using the NDK. It can also be a starting point for your NDK-based application. The NDK-based Minimal application does not process network packets in any way; it only sends and receives them. If the DMA IP is enabled, then it forwards the network packets to the computer memory. You can find more detailed information in [the NDK-FPGA documentation (devel branch) here](https://cesnet.github.io/ndk-fpga/devel/).

**The DMA Medusa IP is not part of the open-source NDK. If the DMA IP is disabled, it is replaced by a loopback. [You can get the NDK, including the DMA Medusa IP and professional support, through our partner BrnoLogic](https://support.brnologic.com/).**

## How to start

Before you get started, there are a few requirements that you need to have.

### Requirements and supported FPGA cards

- To build the FPGA firmware, you must have installed the **Intel Quartus Prime Pro 24.1** or **Xilinx Vivado 2022.2** (depending on the target card), including a valid license.
- We recommend using the **Questa Sim-64 2023.1_2** tool to run HDL verifications (UVM).
- Supported FPGA cards in the NDK framework available as open-source:
    - ReflexCES XpressSX AGI-FH400G card (BOARD_REV=0 is deprecated)
    - Intel Stratix 10 DX FPGA Development Kit (DK-DEV-1SDX-P)
    - Intel Agilex I-Series FPGA Development Kit (DK-DEV-AGI027RES is deprecated)
    - Silicom fb4CGg3@VU9P card (also in variant fb2CGg3@VU9P)
    - Silicom fb2CGhh@KU15P card
    - Silicom N6010 card
    - Bittware IA-420F card
    - AMD/Xilinx Alveo U200
    - AMD/Xilinx Alveo U55C
    - AMD/Xilinx Virtex UltraScale+ FPGA VCU118 Evaluation Kit
- Other supported FPGA cards in the NDK framework but not available as open-source:
    - Netcope NFB-200G2QL card
- To control an FPGA card with an application based on the NDK framework, you also need:
    - [NDK Linux driver and SW tools](https://github.com/CESNET/ndk-sw)

### How to clone the necessary repositories

Just clone the NDK-FPGA repository from GitHub:

```
git clone https://github.com/CESNET/ndk-fpga.git
```

CESNET developers who have access to closed-source repositories can use a single command to clone the repository, including its submodules (from private GitLab):
```
git clone --recursive git@gitlab.liberouter.org:ndk/ndk-fpga.git
```

### Next steps

The [NDK-FPGA documentation (devel branch) in chapter "How to start"](https://cesnet.github.io/ndk-fpga/devel/ndk_core/doc/how_to_start.html) lists further steps for building the FPGA firmware, loading it into the FPGA card and also using it.

## Documentation

We use a documentation system based on the [Sphinx tool](https://www.sphinx-doc.org), which compiles complete documentation from source files in the [reStructuredText](https://docutils.sourceforge.io/rst.html) format. We also use the [Sphinx-vhdl](https://github.com/CESNET/sphinx-vhdl) for generating documentation from the VHDL code. The documentation automatically builds with each contribution to the devel/main branch and is available online here:
- [**NDK-FPGA documentation (main branch)**](https://cesnet.github.io/ndk-fpga/main/)
- [**NDK-FPGA documentation (devel branch)**](https://cesnet.github.io/ndk-fpga/devel/)

### How to manually build documentation

First, you need to install a few Python packages:
```
$ pip3 install --user GitPython
$ pip3 install --user sphinx
$ pip3 install --user sphinx-vhdl
$ pip3 install --user sphinx_rtd_theme
```

Then the documentation is generated simply by issuing these two commands:
```
$ cd doc
$ make html
```

The output is in the `doc/build/index.html` file.

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
- The files located in the `cards/silicom/n6010/src/comp/pmci/pmci_ip` and `cards/silicom/n6010/scripts` folders were taken from the [ofs-n6001 repository](https://github.com/OFS/ofs-n6001) and are subject to the MIT license. Please read [LICENSE.txt file](cards/silicom/n6010/scripts/LICENSE.txt).

## Repository Maintainer

- Jakub Cabal, cabal@cesnet.cz