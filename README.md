# NDK Minimal Application

The Network Development Kit (NDK) allows users to quickly and easily develop new network appliances based on FPGA acceleration cards. The NDK is optimized for high throughput and scalable to support up to 400 Gigabit Ethernet.
 
The Minimal application serves as a simple example of how to build an FPGA application using the Network Development Kit (NDK). It can also be used as a starting point for building your application. The Minimal application does not process network packets in any way, it can only receive and send them. If the DMA module IP is enabled, the network packets are forwarded to the computer memory.

**The DMA module IP is not part of the open-source NDK. If the DMA module IP is disabled, then it is replaced by a loopback. [You can get NDK including DMA Module IP and professional support through our partner BrnoLogic](https://support.brnologic.com/).**

## Requirements, clone and build

- To build FPGA firmware, you must have Intel Quartus Prime Pro 22.2 or Xilinx Vivado 2019.1 (depending on the target card) installed, including a valid license.
- Basic additional repositories which are needed to build the NDK-based Minimal application:
    - [Open FPGA Modules](https://github.com/CESNET/ofm/)
    - [NDK Core](https://github.com/CESNET/ndk-core/)
- Supported FPGA cards in the NDK framework (at least one repository of the supported card must be used for the successful build):
    - [ReflexCES XpressSX AGI-FH400G card](https://github.com/CESNET/ndk-card-agi-fh400g/)
    - [Intel DK-DEV-1SDX-P card](https://github.com/CESNET/ndk-card-dk-dev-1sdx-p/)
    - [Intel DK-DEV-AGI027RES card](https://github.com/CESNET/ndk-card-dk-dev-agi027res/)
    - [Silicom FB4CGG3/FB2CGG3 card](https://github.com/CESNET/ndk-card-fb4cgg3/)
- Other supported FPGA cards in the NDK framework, but not available as open-source:
    - Silicom FB2CGHH card
- To control an FPGA card with an application based on the NDK framework, you need:
    - [NDK Linux driver and SW tools](https://github.com/CESNET/ndk-sw)

### How to clone the necessary repositories

Anyone who wants to try the NDK-based Minimal application, which is available as open-source, must manually clone the repository with the selected (available) submodules:

```
git clone git@github.com:CESNET/ndk-app-minimal.git
cd ndk-app-minimal
git submodule update --init ndk/ofm
git submodule update --init ndk/core
git submodule update --init ndk/cards/agi-fh400g
git submodule update --init ndk/cards/dk-dev-1sdx-p
git submodule update --init ndk/cards/dk-dev-agi027res
git submodule update --init ndk/cards/fb4cgg3
```

CESNET developers who have access to closed-source repositories can use single command to clone a repository, including submodules (private GitLab):
```
git clone --recursive git@gitlab.liberouter.org:ndk/ndk-app-minimal.git
```

### How to build the FPGA firmware

- Go to `build/your_card/` folder in this repository.
- Check or modify `user_const.tcl` file, where you can change the firmware configuration.
- If you do not have a DMA module IP (is not part of the open-source NDK), you must set the `DMA_ENABLE` parameter to `false`.
- Run firmware build in Quartus/Vivado by `make` command in the same folder.

## Documentation

We use a documentation system based on the [Sphinx tool](https://www.sphinx-doc.org), which compiles complete documentation from source files in the [reStructuredText](https://docutils.sourceforge.io/rst.html) format. For generating documentation from VHDL code we use the [Sphinx-vhdl](https://github.com/CESNET/sphinx-vhdl) extension. The documentation automatically builds with each contribution to the devel branch and is available online here:
- [**Minimal NDK Application Docs (public GitHub - built from main branch)**](https://cesnet.github.io/ndk-app-minimal/)
- [**Minimal NDK Application Docs (private GitLab - built from devel branch)**](https://ndk.gitlab.liberouter.org:5051/ndk-app-minimal/)

### How to manually build documentation

First you need to install the sphinx package and theme in python:
```
$ pip3 install --user sphinx
$ pip3 install --user sphinx-vhdl
$ pip3 install --user sphinx_rtd_theme
```

Then the documentation should be able to be generated simply as follows:
```
$ cd doc
$ make html
```

The output is in `doc/build/index.html`

## License

Unless otherwise noted, the content of this repository is available under the BSD 3-Clause License. Please read [LICENSE file](LICENSE).

- See also the license information (in README.md) in each Git submodule.

## Repository Maintainer

- Jakub Cabal, cabal@cesnet.cz
