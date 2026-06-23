# core_const.tcl: Generates constants to the VHDL package and fills them with
# values specified by TCL variables
# Copyright (C) 2022 CESNET, z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Vladislav Valek <valekv@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# NOTE: For detailed description about a purpose of this file, see the
# Parametrization section in the documentation of the NDK-CORE repository.

# Build identification (generated automatically by default)
set BUILD_TIME [format "%d" [clock seconds]]
set BUILD_UID  [format "%d" [exec id -u]]

# ------------------------------------------------------------------------------
# Fixed DMA parameters
# ------------------------------------------------------------------------------
set DMA_RX_FRAME_SIZE_MIN 60
set DMA_TX_FRAME_SIZE_MIN 60

set PCIE_LANES 16
if {$PCIE_ENDPOINT_MODE == 2} {
    set PCIE_LANES 8
}

if {$DMA_TYPE == 4} {
    foreach i [nb_range $ETH_PORTS] {
        set ETH_PORT_TX_MTU($i) 4096
        set ETH_PORT_RX_MTU($i) 4096
    }

    set DMA_RX_FRAME_SIZE_MAX 4096
    set DMA_TX_FRAME_SIZE_MAX 4096
    set DMA_RX_DATA_PTR_W 16
    set DMA_RX_HDR_PTR_W  16

    # This is because the size of the buffer depends on the width of the pointer in TX DMA
    # If the pointer width is set to too big value, the system will automatically
    # cut this value to the highest allowed which is 13.
    if {$DMA_TX_DATA_PTR_W > 13} {
        puts "WARNING: Too big width of TX DMA data pointer: $DMA_TX_DATA_PTR_W! Defaulting to 13."
        set DMA_TX_DATA_PTR_W 13
    }
}

if {!$env(NET_MOD_ENABLE)} {
    set NET_MOD_ARCH "EMPTY"
}

# ------------------------------------------------------------------------------
# Checking of parameter compatibility
# ------------------------------------------------------------------------------

if { $DMA_TYPE == 4 } {
    if {
        !(
          ($PCIE_GEN == 3 && $PCIE_ENDPOINTS == 1 && $PCIE_ENDPOINT_MODE == 0) ||
          ($PCIE_GEN == 3 && $PCIE_ENDPOINTS == 1 && $PCIE_ENDPOINT_MODE == 2) ||
          ($PCIE_GEN == 4 && $PCIE_ENDPOINTS == 1 && $PCIE_ENDPOINT_MODE == 0) ||
          ($PCIE_GEN == 4 && $PCIE_ENDPOINTS == 2 && $PCIE_ENDPOINT_MODE == 1)
        )
    } {
        puts "-----------------------------------------------------------------------------"
        puts "ERROR: Incompatible PCIE_CONF with DMA Calypte IP (DMA_TYPE=4)!"
        puts "-----------------------------------------------------------------------------"
        puts "Try using one of the following configurations for the PCIE_CONF parameter:"
        puts "- PCIE_CONF=1xGen3x16\n- PCIE_CONF=1xGen4x16\n- PCIE_CONF=1xGen3x8LL"
        puts "-----------------------------------------------------------------------------"
        exit 1
    }

    if { $DMA_TX_FRAME_SIZE_MAX > [expr 2**$DMA_TX_DATA_PTR_W -1] } {
        error "The maximum allowed length of a packet is too large and cannot fit to data buffer:\
                DMA_TX_FRAME_SIZE_MAX: $DMA_TX_FRAME_SIZE and DMA_TX_DATA_PTR_W: $DMA_TX_DATA_PTR_W"
    }
} elseif { $DMA_TYPE == 3 } {
    if { $DMA_RX_DATA_PTR_W != 16 || $DMA_RX_HDR_PTR_W != 16 || $DMA_TX_DATA_PTR_W != 16} {
        error "This pointer configuration has never been tested on DMA Medusa: RX_DATA_PTR_W: $DMA_RX_DATA_PTR_W,\
                RX_HDR_PTR_W: $DMA_RX_HDR_PTR_W, TX_DATA_PTR_W: $DMA_TX_DATA_PTR_W!"
    }

    if { $PCIE_ENDPOINT_MODE == 2} {
        error "Incompatible DMA_TYPE: $DMA_TYPE with chosen PCIE_ENDPOINT_MODE: $PCIE_ENDPOINT_MODE\
                and PCIE_LANES: $PCIE_LANES! Try to use PCIE_CONF=1xGen4x16 or PCIE_CONF=1xGen3x16."
    }
}

VhdlPkgProjectText -pkg ndk_fpga_common_pkg $PROJECT_NAME

VhdlPkgStr -pkg ndk_fpga_top_pkg CARD_NAME     $CARD_NAME
VhdlPkgStr -pkg ndk_fpga_top_pkg PCIE_MOD_ARCH $PCIE_MOD_ARCH
VhdlPkgStr -pkg ndk_fpga_top_pkg NET_MOD_ARCH  $NET_MOD_ARCH

VhdlPkgInt -pkg ndk_fpga_top_pkg ETH_PORTS       $ETH_PORTS

VhdlPkgIntArr -pkg ndk_fpga_common_pkg ETH_PORT_SPEED  $ETH_PORTS
VhdlPkgIntArr -pkg ndk_fpga_common_pkg ETH_PORT_CHAN   $ETH_PORTS
VhdlPkgIntArr -pkg ndk_fpga_common_pkg EHIP_PORT_TYPE  $ETH_PORTS
VhdlPkgIntArr -pkg ndk_fpga_common_pkg ETH_PORT_RX_MTU $ETH_PORTS
VhdlPkgIntArr -pkg ndk_fpga_common_pkg ETH_PORT_TX_MTU $ETH_PORTS

VhdlPkgIntArr -pkg ndk_fpga_common_pkg ETH_CHAN_MAP    8

VhdlPkgInt  -pkg ndk_fpga_common_pkg ETH_STREAMS_MODE $ETH_STREAMS_MODE
VhdlPkgBool -pkg ndk_fpga_common_pkg ETH_MAC_BYPASS   $ETH_MAC_BYPASS

# ------------------------------------------------------------------------------
# DMA Channel calculation
# ------------------------------------------------------------------------------
# NOTE: This does not apply when the configured amount of channels is greater
# than 0 on BOTH directions (RX and TX).

# When disabling one of the DMA directions, the amount of channels shall be set
# to 0 in TCL scripts which also correctly generates Device Tree. However, the
# 0 amount of channels would cause problems in the VHDL design regarding signal
# width mismatches. Therefore, when one direction is disabled, the number of
# channels on this one is set to the amount of channels on the enabled
# direction. This ensures matching signal widths in the VHDL design.
#
# When both of the directions are disabled Then each direction is configured
# containing 2 channels which is the minimum currently allowed. Either way, when
# configuriong one direction with 0 channels available, then the corresponding
# DMA controller is not initialized in the design.

VhdlPkgBool -pkg ndk_fpga_common_pkg RX_GEN_EN [expr {$DMA_RX_CHANNELS > 0 ? true : false}]
VhdlPkgBool -pkg ndk_fpga_common_pkg TX_GEN_EN [expr {$DMA_TX_CHANNELS > 0 ? true : false}]

set dma_tx_chans_int $DMA_TX_CHANNELS
set dma_rx_chans_int $DMA_RX_CHANNELS

if {$DMA_RX_CHANNELS == 0} {
    if {$DMA_TX_CHANNELS == 0} {
        set dma_rx_chans_int 2
    } else {
        set dma_rx_chans_int $DMA_TX_CHANNELS
    }
}

if {$DMA_TX_CHANNELS == 0} {
    if {$DMA_RX_CHANNELS == 0} {
        set dma_tx_chans_int 2
    } else {
        set dma_tx_chans_int $DMA_RX_CHANNELS
    }
}
# ------------------------------------------------------------------------------

VhdlPkgInt -pkg ndk_fpga_top_pkg PCIE_LANES         $PCIE_LANES
VhdlPkgInt -pkg ndk_fpga_common_pkg PCIE_GEN           $PCIE_GEN
VhdlPkgInt -pkg ndk_fpga_top_pkg PCIE_ENDPOINTS     $PCIE_ENDPOINTS
VhdlPkgInt -pkg ndk_fpga_top_pkg PCIE_ENDPOINT_MODE $PCIE_ENDPOINT_MODE

VhdlPkgInt  -pkg ndk_fpga_common_pkg DMA_TYPE              $DMA_TYPE
VhdlPkgInt  -pkg ndk_fpga_common_pkg DMA_MODULES           $DMA_MODULES
VhdlPkgInt  -pkg ndk_fpga_common_pkg DMA_ENDPOINTS         $DMA_ENDPOINTS
VhdlPkgInt  -pkg ndk_fpga_common_pkg DMA_RX_CHANNELS       $dma_rx_chans_int
VhdlPkgInt  -pkg ndk_fpga_common_pkg DMA_TX_CHANNELS       $dma_tx_chans_int
VhdlPkgInt  -pkg ndk_fpga_common_pkg DMA_RX_FRAME_SIZE_MAX $DMA_RX_FRAME_SIZE_MAX
VhdlPkgInt  -pkg ndk_fpga_common_pkg DMA_TX_FRAME_SIZE_MAX $DMA_TX_FRAME_SIZE_MAX
#VhdlPkgInt  -pkg ndk_fpga_common_pkg DMA_RX_FRAME_SIZE_MIN $DMA_RX_FRAME_SIZE_MIN
#VhdlPkgInt  -pkg ndk_fpga_common_pkg DMA_TX_FRAME_SIZE_MIN $DMA_TX_FRAME_SIZE_MIN
VhdlPkgBool -pkg ndk_fpga_common_pkg DMA_RX_BLOCKING_MODE $DMA_RX_BLOCKING_MODE
VhdlPkgInt  -pkg ndk_fpga_common_pkg DMA_RX_DATA_PTR_W    $DMA_RX_DATA_PTR_W
VhdlPkgInt  -pkg ndk_fpga_common_pkg DMA_RX_HDR_PTR_W     $DMA_RX_HDR_PTR_W
VhdlPkgInt  -pkg ndk_fpga_common_pkg DMA_TX_DATA_PTR_W    $DMA_TX_DATA_PTR_W

VhdlPkgBool -pkg ndk_fpga_common_pkg DMA_GEN_LOOP_EN      $DMA_GEN_LOOP_EN

# Other parameters
VhdlPkgBool -pkg ndk_fpga_common_pkg TSU_ENABLE    $TSU_ENABLE
VhdlPkgInt  -pkg ndk_fpga_common_pkg TSU_FREQUENCY $TSU_FREQUENCY

VhdlPkgInt -pkg ndk_fpga_top_pkg MEM_PORTS     $MEM_PORTS
VhdlPkgInt -pkg ndk_fpga_top_pkg HBM_PORTS     $HBM_PORTS

VhdlPkgBool -pkg ndk_fpga_common_pkg VIRTUAL_DEBUG_ENABLE   $VIRTUAL_DEBUG_ENABLE
VhdlPkgBool -pkg ndk_fpga_common_pkg DMA_DEBUG_ENABLE       $DMA_DEBUG_ENABLE
VhdlPkgBool -pkg ndk_fpga_common_pkg PCIE_CORE_DEBUG_ENABLE $PCIE_CORE_DEBUG_ENABLE
VhdlPkgBool -pkg ndk_fpga_common_pkg PCIE_CTRL_DEBUG_ENABLE $PCIE_CTRL_DEBUG_ENABLE

VhdlPkgBool -pkg ndk_fpga_common_pkg MEASURE_FREQUENCIES    $MEASURE_FREQUENCIES
VhdlPkgBool -pkg ndk_fpga_common_pkg TS_DEMO_EN             $TS_DEMO_EN
VhdlPkgBool -pkg ndk_fpga_common_pkg LL_MODE                $LL_MODE

