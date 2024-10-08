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

    set ETH_PORT_TX_MTU(0) 4096
    set ETH_PORT_TX_MTU(1) 4096
    set ETH_PORT_TX_MTU(2) 4096
    set ETH_PORT_TX_MTU(3) 4096

    set ETH_PORT_RX_MTU(0) 4096
    set ETH_PORT_RX_MTU(1) 4096
    set ETH_PORT_RX_MTU(2) 4096
    set ETH_PORT_RX_MTU(3) 4096

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

if {$ETH_PORTS == 0} {
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
          ($PCIE_GEN == 4 && $PCIE_ENDPOINTS == 1 && $PCIE_ENDPOINT_MODE == 0)
        )
    } {
        error "Incompatible DMA_TYPE: $DMA_TYPE with chosen PCIE_ENDPOINTS: $PCIE_ENDPOINTS\
                and PCIE_ENDPOINT_MODE: $PCIE_ENDPOINT_MODE!"
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

VhdlPkgProjectText $PROJECT_NAME

VhdlPkgStr CARD_NAME     $CARD_NAME
VhdlPkgStr PCIE_MOD_ARCH $PCIE_MOD_ARCH
VhdlPkgStr NET_MOD_ARCH  $NET_MOD_ARCH

# This is only to ensure the correct package generation.
if {$ETH_PORTS == 0} {
    VhdlPkgInt    ETH_PORTS       1
    VhdlPkgIntArr ETH_PORT_SPEED  1
    VhdlPkgIntArr ETH_PORT_CHAN   1
    VhdlPkgIntArr EHIP_PORT_TYPE  1
    VhdlPkgIntArr ETH_PORT_RX_MTU 1
    VhdlPkgIntArr ETH_PORT_TX_MTU 1
} else {
    VhdlPkgInt    ETH_PORTS       $ETH_PORTS
    VhdlPkgIntArr ETH_PORT_SPEED  $ETH_PORTS
    VhdlPkgIntArr ETH_PORT_CHAN   $ETH_PORTS
    VhdlPkgIntArr EHIP_PORT_TYPE  $ETH_PORTS
    VhdlPkgIntArr ETH_PORT_RX_MTU $ETH_PORTS
    VhdlPkgIntArr ETH_PORT_TX_MTU $ETH_PORTS
}

VhdlPkgInt  ETH_STREAMS_MODE $ETH_STREAMS_MODE
VhdlPkgBool ETH_MAC_BYPASS   $ETH_MAC_BYPASS

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

VhdlPkgBool RX_GEN_EN [expr {$DMA_RX_CHANNELS > 0 ? true : false}]
VhdlPkgBool TX_GEN_EN [expr {$DMA_TX_CHANNELS > 0 ? true : false}]

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

VhdlPkgInt  PCIE_LANES         $PCIE_LANES
VhdlPkgInt  PCIE_GEN           $PCIE_GEN
VhdlPkgInt  PCIE_ENDPOINTS     $PCIE_ENDPOINTS
VhdlPkgInt  PCIE_ENDPOINT_MODE $PCIE_ENDPOINT_MODE

VhdlPkgInt  DMA_TYPE              $DMA_TYPE
VhdlPkgInt  DMA_RX_CHANNELS       $dma_rx_chans_int
VhdlPkgInt  DMA_TX_CHANNELS       $dma_tx_chans_int
VhdlPkgInt  DMA_RX_FRAME_SIZE_MAX $DMA_RX_FRAME_SIZE_MAX
VhdlPkgInt  DMA_TX_FRAME_SIZE_MAX $DMA_TX_FRAME_SIZE_MAX
#VhdlPkgInt  DMA_RX_FRAME_SIZE_MIN $DMA_RX_FRAME_SIZE_MIN
#VhdlPkgInt  DMA_TX_FRAME_SIZE_MIN $DMA_TX_FRAME_SIZE_MIN
VhdlPkgBool DMA_RX_BLOCKING_MODE $DMA_RX_BLOCKING_MODE
VhdlPkgInt  DMA_RX_DATA_PTR_W    $DMA_RX_DATA_PTR_W
VhdlPkgInt  DMA_RX_HDR_PTR_W     $DMA_RX_HDR_PTR_W
VhdlPkgInt  DMA_TX_DATA_PTR_W    $DMA_TX_DATA_PTR_W

VhdlPkgBool DMA_GEN_LOOP_EN      $DMA_GEN_LOOP_EN

# Other parameters
VhdlPkgBool TSU_ENABLE    $TSU_ENABLE
VhdlPkgInt  TSU_FREQUENCY $TSU_FREQUENCY

VhdlPkgInt  MEM_PORTS     $MEM_PORTS
VhdlPkgInt  HBM_PORTS     $HBM_PORTS

VhdlPkgBool VIRTUAL_DEBUG_ENABLE   $VIRTUAL_DEBUG_ENABLE
VhdlPkgBool DMA_DEBUG_ENABLE       $DMA_DEBUG_ENABLE
VhdlPkgBool PCIE_CORE_DEBUG_ENABLE $PCIE_CORE_DEBUG_ENABLE
VhdlPkgBool PCIE_CTRL_DEBUG_ENABLE $PCIE_CTRL_DEBUG_ENABLE

VhdlPkgBool TS_DEMO_EN             $TS_DEMO_EN
