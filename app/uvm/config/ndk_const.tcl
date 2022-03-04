# ndk_const.tcl: Base parameters for Intel FPGA cards
# Copyright (C) 2019 CESNET, z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

# Build identification (generated automatically by default)
set BUILD_TIME [format "%d" [clock seconds]]
set BUILD_UID  [format "%d" [exec id -u]]

VhdlPkgProjectText $PROJECT_NAME

VhdlPkgInt    USER_GENERIC0   $USER_GENERIC0
VhdlPkgInt    USER_GENERIC1   $USER_GENERIC1
VhdlPkgInt    USER_GENERIC2   $USER_GENERIC2
VhdlPkgInt    USER_GENERIC3   $USER_GENERIC3

VhdlPkgBool   ETH_ENABLE      $ETH_ENABLE
VhdlPkgInt    ETH_PORTS       $ETH_PORTS
VhdlPkgIntArr ETH_PORT_SPEED  $ETH_PORTS
VhdlPkgIntArr ETH_PORT_CHAN   $ETH_PORTS
# TODO: MTU is not fully configurable right now
VhdlPkgHexVector MAX_MTU_RX      32 00003FE0
VhdlPkgHexVector MAX_MTU_TX      32 00003FE0

VhdlPkgInt  PCIE_ENDPOINTS     $PCIE_ENDPOINTS
VhdlPkgInt  PCIE_ENDPOINT_MODE $PCIE_ENDPOINT_MODE

VhdlPkgInt  DMA_RX_CHANNELS      $DMA_RX_CHANNELS
VhdlPkgInt  DMA_TX_CHANNELS      $DMA_TX_CHANNELS
VhdlPkgBool DMA_RX_BLOCKING_MODE $DMA_RX_BLOCKING_MODE
VhdlPkgInt  DMA_CROX_CLK_SEL     $DMA_CROX_CLK_SEL

# Other parameters
VhdlPkgBool TSU_ENABLE    $TSU_ENABLE
VhdlPkgInt  TSU_FREQUENCY $TSU_FREQUENCY
VhdlPkgInt  RESET_WIDTH   $RESET_WIDTH
