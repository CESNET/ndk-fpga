# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).
[Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) format is required for commit messages.

## [0.10.0] - 2025-03-25

### Added
- cards: Introduced support for Napatech NT200A02 card.
- cards: Introduced boot controller for the Bittware IA-440i card.
- cards: Introduced DDR4 memory support for the Bittware IA-440i card.
- build: Introduced loading device tree files to verifications.
- core: Introduced parameterizable IOPLL for Altera FPGAs.
- core: Added propagation the PCIE_GEN parameter to the PCIE_CORE module.
- core: Integrated the frequency meter to the fpga_common.
- comp: Introduced MFB MVB Prepender component.
- comp: Introduced the frequency_meter component include Python module.
- comp: Introduced the Python module for MFB Generator component.
- comp: Introduced the Python module for Gen Loop Switch (GLS) component.
- comp: Added function for ORing together all items of an array into one vector in type_pack.
- comp: Added function to resize items of an array in type_pack.
- docs: Introduced NDK performance report.
- uvm: Added interface properties to check correct behavioral in pcie-adapter-ver.
- uvm: Added verification for MVB_MERGE_STREAMS, MFB_FRAME_TRIMMER, MFB_FRAME_EXTENDER, MVB_SHAKEDOWN components.
- uvm: Added sequence_min_max to uvm_logic_vector sequence library.
- uvm: Added the sequence_inverted_gauss sequence.
- uvm: Added support for build device tree in verifications.
- ver: Created mvb speed meter for old verification.

### Changed
- cocotb: Update cocotb verifications for MVB_HASH_TABLE_SIMPLE and MVB_FIFOX.
- build: Added print running time to end of simulation in multiver script.
- cards: Set PCIe Gen5 x8x8 mode as default for IA-440i card.
- cards: Made AGI-FH400G-REV0 card work again with older Quartus.
- core: Added SDM_CTRL architecture compatible with older Quartus.
- core: Revised R-Tile PCIe IP and add Gen4 x16 mode.
- dma: Registered DMA Calypte reset for better timing.
- dma: Refactored DMA Calypte include docs.
- app: Set DMA channels to 32 on IA-440i card in Minimal app.
- app: Used PCIE_CONF in FW build name.
- app: Used 16 channels for DMA Calypte on R-Tile FPGAs.
- uvm: Improved comparing data in scoreboard.

### Removed
- cards: Removed DK-DEV-AGI027RES card support.

### Fixed
- build: Fixed post-place physical optimization directive setting in Vivado.
- cards: Fixed DMA_ENDPOINTS calculation on R-Tile cards.
- core: Fixed multi-region support in DMA Calypte wrapper.
- comp: Fixed setting the 100GBASE-SR4 mode in the Ethernet MGMT.
- comp: Fixed optional PMA_TX_FAULT input in the Ethernet MGMT.
- comp: Fixed fix latency histogram in MEM_TESTER component.
- comp: Fixed test results checks in MEM_TESTER component.
- comp: Removed ambiguous behaviour in MVB_DEMUX component due to DST/DST RDY loop.
- comp: Fixed open ndp_read in dma tests and fix typo in dma_tx test in GLS script.
- comp: Used MTU_PKT instead of LEN_WIDTH in entity and prevent bit overflow in MFB_FRAME_TRIMMER. (BREAKING CHANGE!)
- comp: Increased the length of signals to prevent a bit overflow in MFB_FRAME_EXTENDER. (BREAKING CHANGE!)
- dma: Fixed send stop request after pointers have same values in DMA_CALYPTE.
- uvm: Removed copy sw pointer from HW pointer when driver is shutting down channel in DMA_CALYPTE.
- uvm: Fixed start generating data after first ready is set, reset ocurres.
- uvm: Fixed generating valid signal with specific ready latency on AVST.

## [0.9.0] - 2025-01-13

### Added
- cocotb: Introduced gRPC servicer and server including an example for external process interaction.
- build: Introduced support for IP generation using TCL on Stratix 10 FPGAs.
- cards: Added PCI BAR2 to UltraScale+ cards and Intel FPGA cards with P-Tile (required for DMA Calypte).
- cards: Introduced support for Bittware IA-440i card.
- cards: Introduced support for iWave G35P card.
- core: Introduced implementation of 4x10G and 4x25G network_mod_core for UltraScale+ FPGAs (requires closed-source submodules).
- core: Added option (on by default) to drop frames in TX_MAC_LITE when the link is down.
- comp: Introduced new components: AXIS_ASFIFOX.

### Changed
- cocotb: Reworked Cocotb MI driver.
- build: Unified tcl scripts for IP generation on UltraScale+ cards and Intel FPGA cards with P-Tile.
- build: DMA_DEBUG_ENABLE parameter is passed upon the `make` command.
- build: Made the DMA_MODULES parameter part of the generated VHDL package.
- comp: Replaced /dev/nfb0 by real default device (selected by libnfb) in all pynfb tools.
- comp: Reworked TSU_ASYNC component supporting a timeout.
- card: Enabled support for DMA Calypte on the DK-DEV-1SDX-P card.
- card: Changed the default PCIe configuration on DK-DEV-1SDX-P card to 1xGen4x16.
- docs: Improved the documentation of MFB_FRAME_EXTENDER, MFB_USER_PACKET_GEN.
- dma: Disabled unused speed meters in DMA Medusa (saving FPGA resources).
- dma: Added several optimizations in DMA Calypte (especially timing optimization).
- uvm: Improved sequence_main in APP CORE verification.
- uvm: Improved Network Module verification.
- uvm: Improved DMA Calypte verification.
- ver: Improved DMA Medusa verification (especially removed PTC and PCIe adapters).

### Removed
- core: Removed obsolete PCI generics from FPGA_COMMON.
- core: Removed obsolete parameter DMA_400G_DEMO.
- comp: Removed old unused components (MI_REGISTER_ARRAY, MULTI_FIFO, FIFO_N1, INSPECTOR, TS_SYNC).
- uvm: Removed obsolete revision of UVM packet generator.

### Fixed
- card: Fixed assign constant when DDR_PORTS <=1 on fb2cghh card.
- comp: Fixed assignment of FBE and LBE in PCIE_CQ_AXI2MFB module.
- dma: Deactivated relaxed ordering (considered unsafe) in RX DMA Calypte.
- dma: Allowed only one in-progress update per channel in RX DMA Medusa.
- dma: Allowed a channel to be turned off only when an update in RX DMA Medusa is not in progress.
- dma: Propagated the DBG_CNTR_EN parameter to the DMA_CTRL module in RX DMA Medusa (option to save FPGA resources).
- dma: Fixed size of FIFO for PCIe response address in TX DMA Medusa.
- dma: Fixed the calculation of buffers size in DMA Medusa.
- dma: Fixed early PCIe header drop in RX DMA Calypte.
- dma: Fixed enable of LBE register when generating BE vector in TX DMA Calypte.
- dma: Fixed FIFOX_MULTI memory type in TX DMA Calypte for better compatibilty with Altera FPGAs.
- app: Fixed important missing generics for the MEM_LOGGER instance in Minimal app.
- uvm: Fixed deprecated KeysView import in FlowTest Python generator.
- uvm: Fixed correction of protocol weights after the last MPLS in the UVM packet generator.

## [0.8.0] - 2024-11-19

### Added
- cocotb: Introduced generator of random integers.
- cocotb: Introduced MVB rate limiter.
- build: Introduced EXPERIMENTAL env.sh file with mandatory environment variables.
- build: Introduced PLATFORM_TAGS variable for platform, replacement for SYNTH_FLAGS(TOOL).
- build: Introduced templates for DTS generation.
- cards: Introduced support for Terasic A2700 Accelerator card.
- comp: Introduced new components: MFB_MVB_APPENDER, MVB_ITEM_COLLISION_RESOLVER, MVB_GATE, MEM_CLEAR.
- comp: Added packages for statistics processing in Data Logger component.
- core: Added MISC signals between Top-Level and APP/PCIE/NET core.
- core: Added optional low latency mode in Network Module for HFT applications.
- dma: Added performance counters to measure blocking behavior in RX DMA Calypte.
- uvm: Added support of the CMAC variant in Network Module verification.
- ver: Added meters to AVST(PCIE) and AXI(PCIE) for the old verification.
- pkg: Added two functions for slv array concatenation to TYPE_PACK.
- ci: Introduced checking of commit messages in MR using commitlint.

### Changed
- cocotb: Refactored implementation of MVB transactions and their usage in drivers and monitors.
- cocotb: Used prepare.sh + pyproject.toml instead of dep. list in cocotb top-level simulation.
- comp: Improved statistics processing for Data Logger component.
- comp: Refactored implementation of Histogramer component.
- comp: Refactored implementation of TCAM2 component.
- comp: Refactored implementation of MVB_TCAM component.
- core: Enabled Device Tree on all PCIe endpoints. This is required for proper identification of PCIe endpoints when bifurcation is enabled.
- core: Improved PCIe core and DMA Medusa optional debug telemetry.
- docs: Improved NDK-FPGA documentation.
- uvm: Improved print of MVB transaction for APP-UVM verifications.

### Removed
- comp: Remove old unused components (CLK_GEN, SQUARER, CAM, LED_CTRL, DMA_ASFIFO*, PAC_STATS*,
RATE_LIM*, FIFO_PIPE, HYPER_PIPE, WATCHDOG*).

### Fixed
- cocotb: Fixed SOF/EOF error checking in cocotb MFB monitor.
- comp: Fixed histogram box update in Histogramer component.
- core: Fixed width of demo/testing ports in Network Module.
- dma: Fixed MFB transaction size in DMA Medusa Updater module.
- uvm: Fixed LOGIC_VECTOR_ARRAY sequencer, the DB registration macro is now parameterized.
- uvm: Fixed count speed in MFB bus.
- ver: Fixed lot of small bugs in PCIe transactions in old verifications.

## [0.7.2] - 2024-10-17

### Fixed

- Fixed missing prefix DMA Medusa jenkins verification script.
- NFB-200G2QL: Fixed missing lock DNA_PORT2E to X0Y1 due to different Chip ID in each SLRs (private submodule).
- NFB-200G2QL: Fixed all PCIE paths for pblock (private submodule).

## [0.7.1] - 2024-10-16

### Fixed

- Fixed PCIE0 path for pblock to SLR1 on Netcope NFB-200G2QL card (private submodule).
- Fixed single-bit input problem on Agilex DSP counters in new Quartus.
- Fixed coding style in lots of files.
- Fixed Modules.tcl paths due to compatibility with new NDK-FPGA in external APPs.
- Fixed verification jenkins files.
- Fixed build jenkins files of APP-Minimal.

## [0.7.0] - 2024-10-09

- Initial release of NDK-FPGA. The changelog for the previous versions of this
  repository (formerly known as ndk-app-minimal) was not maintained,
  so the changelog starts here.
