# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).
[Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) format is required for commit messages.

## [0.12.0] - 2025-10-02

### Added
- cocotb: Added basic nvm-sim support.
- cocotb: Added support for Silicom FB2CDG1 card in top-level-sim.
- cards: Added support for IA-440i card with AGIB023R18A1E1VC.
- cards: Added external PPS support on N6010, IA-440i, agi-fh400g cards.
- cards: Introduced support for boot controller for Alveo-U200 card.
- core: Introduced support for external PPS signal.
- comp: Introduced spookyhash component.
- comp: Introduced MFB_SWITCH_SIMPLE component.
- comp: Added IPv4/UDP support to MFB Generator.
- docs: Introduced Known Limitations section in NDK documentation.
- dma: Introduced support for wide pointers over 16 bits in DMA Calypte.
- ci: Introduced vhdl-style-guide tool to check VHDL in CI stage.

### Changed
- cocotb: Huge improved cocotb enviroment.
- build: Updated default Agilex device in build system.
- cards: Enabled experimental configuration PCIE_CONF=1xGen5x16 for AGI-FH400G card.
- core: Used UNITID to route to individual DMA endpoints instead of tags.
- core: Improved link status decoding in MII adapter.
- core: Improved sequence decoder, add sequence, remote fault, etc.
- core: Adjusted HDM_MFB_FIFO_DEPTH for up to 64 MPS PCIe transactions.
- comp: Added optional input MFB FIFO to MFB_SPLITTER and MFB_MERGER components.
- docs: Improved documentation of NDK-FPGA.
- uvm: Improved PCIE_MOD and NET_MOD verifications.
- uvm: Improved DMA Calypte verification.
- uvm: Improved UVM verification framework.
- uvm: Improved MTU packet support in UVM.
- sw: Updated recommended tool versions, see README.md file.
- ci: Improved Jenkins files for verifications.

### Removed
- cocotb: Removed old cocotb examples.
- comp: Removed old simulation of asfifo_bram.

### Fixed
- cocotb: Fixed support multiple completions for one request (large MI reads).
- cards: Fixed case-sensitive F-Tile constraints.
- cards: Fixed pull-ups to QSFP_MODPRS_N and QSFP_INT_N on N6010 card.
- cards: Fixed name of PCIE clock for x8 PCIe endpoint on Alveo-U55C.
- cards: Added temporary underclocking of R-Tile PCIe Gen5x16 IP on IA440i card.
- cards: Replaced XCI files with TCL scripts on Alveo-U55C.
- core: Fixed dma_ports_per_ep in dts_pcie_ctrl_dbg.
- core: Fixed missing PCIE_ENDPOINTS in dts_ndp_core_main_mi.
- core: Used full MAC for 40GbE on Ultrascale+ FPGAs.
- core: Fixed MAC link status for 10/25G Intel E-tile FPGAs.
- core: Fixed HDM_MFB_FIFO_DEPTH calculation, MPS is in dwords
- core: Removed unused PFC ports for compatibility with Quartus 25.1
- core: Removed GLS nodes in DeviceTree when disabled.
- core: Fixed Straddling mechanism for AMD PCIe AXI/MFB converters.
- core: Fixed link error timeout counter logic in MII adapter.
- core: Fixed local fault sequence decoding on 10GE links.
- comp: Removed disable_chainout port from tennm_mac in DSP atom, necessary for Quartus 25.1.
- comp: Fixed MVB pipe settings in METADATA_EXTRACTOR.
- comp: Fixed case-sensitive constraints in ASYNC_OPEN_LOOP.
- comp: Reduced MFB splitter array range.
- dma: Fixed reset internal EOF_POS value in DMA Calypte.
- dma: Fixed derivation of channel index from metadata in DMA Calypte.
- uvm: Fixed generating vld when src_rdy is zero in MVB driver.
- uvm: Fixed byte ordering in LBUS/CMAC UVM monitor.
- sw: Fixed path for GLS using "nfb-bus -l" in GLS script.

## [0.11.0] - 2025-07-10

### Added
- cocotb: Added R/F-Tile support to top-level-sim.
- cards: Added custom QSFP I2C controller to Devicetree on IA-440I.
- cards: Added second BMC node for QSFP I2C access on IA-440I.
- cards: Introduced preliminary support for Silicom fb2CDg1@AGM39D-2 (ThunderFjord) card.
- core: Added support for custom QSFP_I2C controllers.
- core: Added option to remap QSFP lanes to Ethernet channels in Network module.
- comp: Added new stats counters to RX/TX_MAC_LITE component.
- comp: Introduced AXIS_SWITCH, AXIS_MERGER, AXIS_SPLITTER components.
- comp: Added tuser signal to AXI2MFB, AXI_PIPE components.
- comp: Added option to disable shared regions in MFB_MVB_PREPENDER, MFB_FRAME_EXTENDER, MFB_USER_PACKET_GEN.
- comp: Added the ofm-gls commandline Python tool for Gen Loop Switch (GLS) component.
- docs: Introduced documentation of top-level-sim and verification enviroment based on cocotb.
- uvm: Added option to generate broadcast MAC addresses to the flowtest sequence.

### Changed
- cocotb: Improved AXI-Stream monitor/driver.
- cards: Overclocked PCIe module to 500MHz for IA-440i card.
- core: Improved DeviceTree generation.
- core: Improved timing in PTC, MTC and Network module.
- comp: Changed dynamic VHDL assertion to PSL assertions.
- comp: Updated the Python module for MFB Generator and Gen Loop Switch (GLS) component.
- comp: Improved MFB MVB Prepender, Shakedown, Packet Planner, MVB Fork components.
- comp: Added and used more error inputs to RX_MAC_LITE.
- comp: Allowed statistics counting when RX_MAC_LITE is disabled.
- comp: Allowed frame dropping when TX_MAC_LITE is disabled.
- docs: Improved NDK-FPGA documentation.
- uvm: Changed data type of the conf_ipv6 and conf_ipv4 in APP-UVM.
- uvm: Improved PCIE_MOD and NET_MOD verifications.
- uvm: Improved packet generators.
- ver: Improved old verification framework.

### Removed
- comp: Removed unused constraints in CrossbarX module.
- uvm: Removed byte_array_* environment and agent.
- ver: Removed MTC, PTC old verifications.

### Fixed
- cards: Set PCIe and DMA pblocks on Alveo U55C.
- cards: Split general constraints into sets of common and specific constraints on AGI-FH400G.
- cards: Fixed power management settings for AGI-FH400G board revision 2.
- cards: Fixed fb2cghh BMC driver.
- core: Fixed CLK delta delay problem in NetMod.
- core: Fixed number of Eth streams for Mode 1 in DeviceTree.
- core: Adjusted width of signals/ports for TS Demo.
- app: Fixed TSU connection in Minimal APP UVM testbench.
- dma: Fixed generation of unaligned transactions by MTU.
- uvm: Fixed the division error in stats count when numbers of values is zero.
- uvm: Changed register macro to register macro with parameter in uvm_logic_vector_array.
- uvm: Changed parent class sequence sequence_lib_pcie_rx.
- uvm: Fixed assign start time to uvm_logic_vector_array::sequence_item from avst::sequence_item.
- uvm: Added address when address number is less that two in sequence_flowtest.
- ver: Fixed error report of PCIe trans over PAGE.
- ver: Check MPS with dword instead bytes.

## [0.10.2] - 2025-03-26

### Fixed
- comp: Added missing resize for gen_offset signal assignment in MFB_FRAME_EXTENDER.
- comp: Fixed misstyped variable in the GLS Python module.

## [0.10.1] - 2025-03-26

### Fixed
- comp: Fixed width of some rx_mvb_* signals in MFB_FRAME_EXTENDER.
- comp: Fixed width of s_rx_new_len signal in MFB_FRAME_TRIMMER.
- app: Fixed DDR reset timing issues in MEM_TESTER_WRAP module.
- uvm: Fixed CLK_ETH in E-Tile and CMAC verification testbenches.

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
