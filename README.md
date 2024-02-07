# NDK Minimal Application

This repository contains a minimal (reference) application (NDK-APP-Minimal) built on top of the Network Development Kit (NDK) for FPGA acceleration cards. The NDK allows users to quickly and easily develop FPGA-accelerated network applications. The NDK is optimized for high throughput and scalability to support up to 400 Gigabit Ethernet.
 
The NDK-based Minimal application is a simple example of how to build an FPGA application using the NDK. It can also be a starting point for your NDK-based application. The NDK-based Minimal application does not process network packets in any way; it only sends and receives them. If the DMA IP is enabled, then it forwards the network packets to the computer memory. You can find more detailed information in [the NDK-APP-Minimal documentation (devel branch) here](https://cesnet.github.io/ndk-app-minimal/devel/).

**The DMA Medusa IP is not part of the open-source NDK. If the DMA IP is disabled, it is replaced by a loopback. [You can get the NDK, including the DMA Medusa IP and professional support, through our partner BrnoLogic](https://support.brnologic.com/).**

## How to start

Before you get started, there are a few requirements that you need to have. Among these are repositories. We describe how and which to clone.

### Requirements and supported FPGA cards

- To build the FPGA firmware, you must have installed the **Intel Quartus Prime Pro 22.4** or **Xilinx Vivado 2022.2** (depending on the target card), including a valid license.
- We recommend using the **Questa Sim-64 2023.1_2** tool to run HDL verifications (UVM).
- Basic additional repositories which are needed to build the NDK-based Minimal application:
    - [Open FPGA Modules](https://github.com/CESNET/ofm/)
    - [NDK Core](https://github.com/CESNET/ndk-core/)
    - [FPGA cards files for the NDK](https://github.com/CESNET/ndk-cards-open/) (available as open-source)
- Supported FPGA cards in the NDK framework available as open-source:
    - ReflexCES XpressSX AGI-FH400G card
    - Intel Stratix 10 DX FPGA Development Kit (DK-DEV-1SDX-P)
    - Intel Agilex I-Series FPGA Development Kit (DK-DEV-AGI027RES)
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

Anyone who wants to try the NDK-based Minimal application has to manually clone the repository with the Minimal application and some submodules. You certainly have to clone the OFM and Core submodules, though only the submodule with the target card is necessary:

```
git clone https://github.com/CESNET/ndk-app-minimal.git
cd ndk-app-minimal
git submodule update --init ndk/ofm
git submodule update --init ndk/core
git submodule update --init ndk/cards
```

CESNET developers who have access to closed-source repositories can use a single command to clone the repository, including its submodules (from private GitLab):
```
git clone --recursive git@gitlab.liberouter.org:ndk/ndk-app-minimal.git
```

### Next steps

The [NDK-APP-Minimal documentation (devel branch) in chapter "How to start"](https://cesnet.github.io/ndk-app-minimal/devel/ndk_core/doc/how_to_start.html) lists further steps for building the FPGA firmware, loading it into the FPGA card and also using it.

## Documentation

We use a documentation system based on the [Sphinx tool](https://www.sphinx-doc.org), which compiles complete documentation from source files in the [reStructuredText](https://docutils.sourceforge.io/rst.html) format. We also use the [Sphinx-vhdl](https://github.com/CESNET/sphinx-vhdl) for generating documentation from the VHDL code. The documentation automatically builds with each contribution to the devel/main branch and is available online here:
- [**NDK-APP-Minimal documentation (main branch)**](https://cesnet.github.io/ndk-app-minimal/main/)
- [**NDK-APP-Minimal documentation (devel branch)**](https://cesnet.github.io/ndk-app-minimal/devel/)

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

## Repository Maintainer

- Jakub Cabal, cabal@cesnet.cz
