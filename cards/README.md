# FPGA cards files with open support for the NDK

This repository contains an open-source extension of the Network Development Kit (NDK) to support the selected FPGA cards.
- The NDK allows users to quickly and easily develop new network applications based on FPGA acceleration cards.
- You can build the FPGA firmware for this card using the [NDK-APP-Minimal application](https://github.com/CESNET/ndk-app-minimal/). The NDK-APP-Minimal is a reference application based on the NDK.
- The [NDK-APP-Minimal documentation](https://cesnet.github.io/ndk-app-minimal/) lists steps for building the FPGA firmware, loading it into the FPGA card, and also using it in the chapter "How to start".

## License

Unless otherwise noted, the content of this repository is available under the BSD 3-Clause License. Please read [LICENSE file](LICENSE).

- The .ip files located in the `<VENDOR>/<CARD_NAME>/src/ip/` folder were generated in the Intel Quartus Prime Pro, and their use may be subject to additional license agreements.
- The .xci files located in the `<VENDOR>/<CARD_NAME>/src/ip/` folder were generated in the Xilinx Vivado, and their use may be subject to additional license agreements.
- The files located in the `silicom/n6010/src/comp/pmci/pmci_ip` and `silicom/n6010/scripts` folders were taken from the [ofs-n6001 repository](https://github.com/OFS/ofs-n6001) and are subject to the MIT license. Please read [LICENSE.txt file](silicom/n6010/scripts/LICENSE.txt).

## Repository Maintainer

- Jakub Cabal, cabal@cesnet.cz