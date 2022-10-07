# NDK Minimal Application

This repository contains a minimal (reference) application (NDK-APP-Minimal) built on top of the Network Development Kit (NDK) platform for FPGA acceleration cards. The NDK allows users to quickly and easily develop new network applications based on FPGA acceleration cards. The NDK is optimized for high throughput and scalability to support up to 400 Gigabit Ethernet.
 
The NDK-based Minimal application is a simple example of how to build an FPGA application using the NDK. It can also be a starting point for your own NDK-based application. The NDK-based Minimal application does not process network packets in any way; it only sends and receives them. If the DMA IP is enabled, then it forwards the network packets to the computer memory. You can find more detailed information in [the NDK-APP-Minimal documentation here](https://cesnet.github.io/ndk-app-minimal/).

**The DMA IP is not part of the open-source NDK. If the DMA IP is disabled, it is replaced by a loopback. [You can get the NDK, including the DMA IP and professional support, through our partner BrnoLogic](https://support.brnologic.com/).**

## How to start

Before you get started, there are a few requirements that you need to have. Among these are repositories. We describe how and which to clone.

### Requirements and supported FPGA cards

- To build the FPGA firmware, you must have installed the **Intel Quartus Prime Pro 22.2** or **Xilinx Vivado 2019.1** (depending on the target card), including a valid license.
- Basic additional repositories which are needed to build the NDK-based Minimal application:
    - [Open FPGA Modules](https://github.com/CESNET/ofm/)
    - [NDK Core](https://github.com/CESNET/ndk-core/)
- Supported FPGA cards in the NDK framework (at least one repository of the supported card must be used for the build to succeed):
    - [ReflexCES XpressSX AGI-FH400G card](https://github.com/CESNET/ndk-card-agi-fh400g/)
    - [Intel DK-DEV-1SDX-P card](https://github.com/CESNET/ndk-card-dk-dev-1sdx-p/)
    - [Intel DK-DEV-AGI027RES card](https://github.com/CESNET/ndk-card-dk-dev-agi027res/)
    - [Silicom FB4CGG3/FB2CGG3 card](https://github.com/CESNET/ndk-card-fb4cgg3/)
- Other supported FPGA cards in the NDK framework but not available as open-source:
    - Silicom FB2CGHH card
- To control an FPGA card with an application based on the NDK framework, you also need:
    - [NDK Linux driver and SW tools](https://github.com/CESNET/ndk-sw)

### How to clone the necessary repositories

Anyone who wants to try the NDK-based Minimal application has to manually clone the repository with the Minimal application and some submodules. You certainly have to clone the OFM and Core submodules, though only the submodule with the target card is necessary:

```
git clone https://github.com/CESNET/ndk-app-minimal.git
cd ndk-app-minimal
git submodule update --init ndk/ofm
git submodule update --init ndk/core
git submodule update --init ndk/cards/agi-fh400g
git submodule update --init ndk/cards/dk-dev-1sdx-p
git submodule update --init ndk/cards/dk-dev-agi027res
git submodule update --init ndk/cards/fb4cgg3
```

CESNET developers who have access to closed-source repositories can use a single command to clone the repository, including its submodules (from private GitLab):
```
git clone --recursive git@gitlab.liberouter.org:ndk/ndk-app-minimal.git
```

### Next steps

The [NDK-APP-Minimal documentation in chapter "How to start"](https://cesnet.github.io/ndk-app-minimal/) lists further steps for building the FPGA firmware, loading it into the FPGA card and also using it.

## Documentation

We use a documentation system based on the [Sphinx tool](https://www.sphinx-doc.org), which compiles complete documentation from source files in the [reStructuredText](https://docutils.sourceforge.io/rst.html) format. We also use the [Sphinx-vhdl](https://github.com/CESNET/sphinx-vhdl) for generating documentation from the VHDL code. The documentation automatically builds with each contribution to the devel/main branch and is available online here:
- [**NDK-APP-Minimal documentation (public GitHub - built from the main branch)**](https://cesnet.github.io/ndk-app-minimal/)
- [**NDK-APP-Minimal documentation (private GitLab - built from the devel branch)**](https://ndk.gitlab.liberouter.org:5051/ndk-app-minimal/)

### How to manually build documentation

First, you need to install the sphinx package and theme in python:
```
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

## License

Unless otherwise noted, the content of this repository is available under the BSD 3-Clause License. Please read [LICENSE file](LICENSE).

- See also the license information (in README.md) in each Git submodule.

## Repository Maintainer

- Jakub Cabal, cabal@cesnet.cz
