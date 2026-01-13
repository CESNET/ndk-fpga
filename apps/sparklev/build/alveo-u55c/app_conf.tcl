# app_conf.tcl: User parameters for AMD Alveo U55C Card
# Copyright 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

# ------------------------------------------------------------------------------
# PCIe parameters (can be overriden via environment variables coming from the Makefile):
# ------------------------------------------------------------------------------
# Supported combinations for this card:
# 1x PCIe Gen3 x16  -- PCIE_GEN=3 and PCIE_ENDPOINT_MODE=0 (Note: default configuration)
# 1x PCIe Gen4 x8x8 -- PCIE_GEN=4 and PCIE_ENDPOINT_MODE=1
# 1x PCIe Gen3 x8   -- PCIE_GEN=3 and PCIE_ENDPOINT_MODE=2 
# 1x PCIe Gen4 x4   -- PCIE_GEN=4 and PCIE_ENDPOINT_MODE=3
# ------------------------------------------------------------------------------

# Set default PCIe configuration
set PCIE_CONF "1xGen3x16"
if { [info exist env(PCIE_CONF)] } {
    set PCIE_CONF $env(PCIE_CONF)
}

# Parsing PCIE_CONF string to list of parameters
set pcie_conf_list [ParsePcieConf $PCIE_CONF]

# PCIe Generation:
# 3 = PCIe Gen3
# 4 = PCIe Gen4
set PCIE_GEN           [lindex $pcie_conf_list 1]
# PCIe endpoints:
# 1 = 1 PCIe endpints
# 2 = 2 PCIe endpints
set PCIE_ENDPOINTS     [lindex $pcie_conf_list 0]
# PCIe endpoint mode:
# 0 = 1x16 lanes
# 1 = 2x8  lanes (bifurcation)
# 2 = 1x8  lanes
# 3 = 1x4  lanes
set PCIE_ENDPOINT_MODE [lindex $pcie_conf_list 2]

# ------------------------------------------------------------------------------
# DMA parameters:
# ------------------------------------------------------------------------------
# This variable can be set in COREs *.mk file or as a parameter when launching the make
set DMA_TYPE              $env(DMA_TYPE)
# The minimum number of RX/TX DMA channels is 2.
set C2H_DMA_CHANNELS      8
set H2C_DMA_CHANNELS      8 
# Maximums size of a packet transferred througb DMA in bytes
set DMA_PKT_SIZE_MAX      4096 
# Enable Gen Loop switch for DMA
set DMA_GEN_LOOP_EN       true
# Separately enable each of the DMA controllers
set C2H_DMA_GEN_EN       true
set H2C_DMA_GEN_EN       true

# ------------------------------------------------------------------------------
# Other parameters:
# ------------------------------------------------------------------------------
set PROJECT_NAME "SPARKLEV"
set PROJECT_VARIANT "$PCIE_CONF"
set PROJECT_VERSION [exec cat ../../../../VERSION]

# Enables debug probes and counters in the DMA Module (Medusa)
set DMA_DEBUG_ENABLE       $env(DMA_DEBUG_ENABLE)
# Enables debug probes and counters in the PCIe Module (PCIe Core arch: USP and P-Tile and PCIe Ctrl)
set PCIE_DEBUG_ENABLE false
# Select architecture of the user core
set USR_CORE_ARCH $env(USR_CORE_ARCH)

# ------------------------------------------------------------------------------
# Constant parameters (do not change)
# ------------------------------------------------------------------------------
set CARD_NAME "ALVEO_U55C"
# Achitecture of Clock generator
set CLOCK_GEN_ARCH "USP"
# Achitecture of PCIe module
set PCIE_MOD_ARCH "USP_PCIE4C"
# Achitecture of SDM/SYSMON module
set SDM_SYSMON_ARCH "USP_IDCOMP"
# Boot controller type
set BOOT_TYPE 1

# Build identification (generated automatically by default)
set BUILD_TIME [format "%d" [clock seconds]]
set BUILD_UID  [format "%d" [exec id -u]]

set PCIE_LANES 16
if {$PCIE_ENDPOINT_MODE == 2} {
    set PCIE_LANES 8
} elseif {$PCIE_ENDPOINT_MODE == 3} {
    set PCIE_LANES 4
}

# Widths of pointers for data/headers
set C2H_DMA_PTR_WIDTH 16
set H2C_DMA_PTR_WIDTH 13

# ------------------------------------------------------------------------------
# Checking of parameter compatibility
# ------------------------------------------------------------------------------

if {!(($PCIE_ENDPOINTS == 1 && $PCIE_GEN == 3 && $PCIE_ENDPOINT_MODE == 0) ||
      ($PCIE_ENDPOINTS == 1 && $PCIE_GEN == 3 && $PCIE_ENDPOINT_MODE == 2) ||
      ($PCIE_ENDPOINTS == 1 && $PCIE_GEN == 4 && $PCIE_ENDPOINT_MODE == 3) ||
      ($PCIE_ENDPOINTS == 2 && $PCIE_GEN == 4 && $PCIE_ENDPOINT_MODE == 1)) } {
    error "Incompatible PCIe configuration: PCIE_ENDPOINTS = $PCIE_ENDPOINTS, PCIE_GEN = $PCIE_GEN, PCIE_ENDPOINT_MODE = $PCIE_ENDPOINT_MODE!
Allowed PCIe configurations:
- 1xGen3x16  -- PCIE_GEN=3, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=0
- 1xGen3x8LL -- PCIE_GEN=3, PCIE_ENDPOINTS=1, PCIE_ENDPOINT_MODE=2
- 2xGen4x8x8 -- PCIE_GEN=4, PCIE_ENDPOINTS=2, PCIE_ENDPOINT_MODE=1"
}

VhdlPkgProjectText $PROJECT_NAME

VhdlPkgStr PCIE_MOD_ARCH            $PCIE_MOD_ARCH
VhdlPkgInt PCIE_LANES               $PCIE_LANES
VhdlPkgInt PCIE_GEN                 $PCIE_GEN
VhdlPkgInt PCIE_ENDPOINTS           $PCIE_ENDPOINTS
VhdlPkgInt PCIE_ENDPOINT_MODE       $PCIE_ENDPOINT_MODE
VhdlPkgBool PCIE_CORE_DEBUG_ENABLE  $PCIE_DEBUG_ENABLE
VhdlPkgBool PCIE_CTRL_DEBUG_ENABLE  $PCIE_DEBUG_ENABLE


VhdlPkgBool C2H_DMA_GEN_EN    $C2H_DMA_GEN_EN
VhdlPkgBool H2C_DMA_GEN_EN    $H2C_DMA_GEN_EN
VhdlPkgInt C2H_DMA_CHANNELS   $C2H_DMA_CHANNELS
VhdlPkgInt H2C_DMA_CHANNELS   $H2C_DMA_CHANNELS
VhdlPkgInt DMA_PKT_SIZE_MAX   $DMA_PKT_SIZE_MAX
VhdlPkgInt C2H_DMA_PTR_WIDTH  $C2H_DMA_PTR_WIDTH
VhdlPkgInt H2C_DMA_PTR_WIDTH  $H2C_DMA_PTR_WIDTH
VhdlPkgBool DMA_DEBUG_ENABLE  $DMA_DEBUG_ENABLE
VhdlPkgBool DMA_GEN_LOOP_EN   $DMA_GEN_LOOP_EN
