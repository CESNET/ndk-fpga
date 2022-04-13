# NDK Minimal Application

The Network Development Kit (NDK) allows users to quickly and easily develop new network appliances based on FPGA acceleration cards. The NDK is optimized for high throughput and scalable to support up to 400 Gigabit Ethernet.
 
The Minimal application serves as a simple example of how to build an FPGA application using the Network Development Kit (NDK). It can also be used as a starting point for building your own application. The Minimal application does not process network packets in any way, it can only receive and send them. If the DMA module IP is enabled, the network packets are forwarded to the computer memory.

**The DMA module IP is not part of the open-source NDK. If the DMA module IP is disabled, then it is replaced by a loopback. [You can get NDK including DMA Module IP and professional support through our partner BrnoLogic](https://support.brnologic.com/)**

## Requirements

- To build FPGA firmware, you must have Intel Quartus Prime Pro 21.4 installed, including a valid license.
- Additional repositories (minimum - available as open-source) are needed to build the NDK design for the FPGA:
    - [NDK Core](https://github.com/CESNET/ndk-core/)
    - [DK-DEV-1SDX-P card for NDK](https://github.com/CESNET/ndk-card-dk-dev-1sdx-p/)
    - [DK-DEV-AGI027RES card for NDK](https://github.com/CESNET/ndk-card-dk-dev-agi027res/)
    - [Open FPGA Modules](https://github.com/CESNET/ofm/)
- [NDK Linux driver and SW tools](https://github.com/CESNET/ndk-sw)

### How to clone the necessary repositories

Anyone who wants to try the NDK-based Minimal application, which is available as open-source, must manually clone the repository with the selected (available) submodules:

```
git clone https://github.com/cesnet/ndk-app-minimal.git
git submodule update --init ndk/ofm
git submodule update --init ndk/core
git submodule update --init ndk/cards/dk-dev-1sdx-p
git submodule update --init ndk/cards/dk-dev-agi027res
```

CESNET developers who have access to closed-source repositories can use single command to clone a repository, including submodules (private GitLab):
```
git clone --recursive git@gitlab.liberouter.org:ndk/ndk-app-minimal.git
```

## Documentation

We use a documentation system based on the [Sphinx tool](https://www.sphinx-doc.org), which compiles complete documentation from source files in the [reStructuredText](https://docutils.sourceforge.io/rst.html) format. The documentation automatically build with each contribution to the devel branch and is available online here:
- [**Minimal NDK Application Docs (public GitHub)**](https://cesnet.github.io/ofm/ndk-app-minimal/)
- [**Minimal NDK Application Docs (private GitLab)**](https://ndk.gitlab.liberouter.org:5051/ndk-app-minimal/)

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
