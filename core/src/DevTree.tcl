proc dts_build_netcope {} {
    # =========================================================================
    # MI ADDRESS SPACE
    # Changes must also be made manually in VHDL package:
    # <NDK-CORE_root_directory>/intel/src/mi_addr_space_pkg.vhd
    # =========================================================================
    set ADDR_TEST_SPACE "0x00000000"
    set ADDR_SDM_SYSMON "0x00001000"
    set ADDR_BOOT_CTRL  "0x00002000"
    set ADDR_ETH_PMD    "0x00003000"
    set ADDR_TSU        "0x00004000"
    set ADDR_GEN_LOOP   "0x00005000"
    set ADDR_ETH_MAC    "0x00008000"
    set ADDR_JTAG_IP    "0x00010000"
    set ADDR_DMA_MOD    "0x01000000"
    set ADDR_PCIE_DBG   "0x01400000"
    set ADDR_ETH_PCS    "0x00800000"
    set ADDR_USERAPP    "0x02000000"

    # =========================================================================
    # Top level Device tree file
    # =========================================================================
    set    ret ""
    set    mi_idx 0

    global CARD_NAME DT_PROJECT_TEXT PROJECT_VARIANT PROJECT_VERSION

    append ret "card-name = \"$CARD_NAME\";"
    if { [info exists DT_PROJECT_TEXT] } {
        append ret "project-name = \"$DT_PROJECT_TEXT\";"
    }
    if { [info exists PROJECT_VARIANT] } {
        append ret "project-variant = \"$PROJECT_VARIANT\";"
    }
    if { [info exists PROJECT_VERSION] } {
        append ret "project-version = \"$PROJECT_VERSION\";"
    }

    # Create MI bus node
    append ret "mi$mi_idx: mi_bus$mi_idx {"
    append ret "#address-cells = <1>;"
    append ret "#size-cells = <1>;"

    append ret "compatible = \"netcope,bus,mi\";"
    append ret "resource = \"PCI0,BAR0\";"
    append ret "width = <0x20>;"

    global BOOT_TYPE
    # BOOT_TYPE overview:
    # ===================
    # 0 = NO boot controller (Intel Devkits)
    # 1 = AXI QSPI + ICAP controller (AMD Alveo cards)
    # 2 = Generic flash + custom BMC controller (Silicom fb4CGg3@VU9P, Netcope NFB-200G2QL, ReflexCES AGI-FH400G)
    # 3 = AXI QSPI + custom BMC controller (Silicom fb2CGhh@KU15P)
    # 4 = ASx4 BOOT via Intel SDM client (Bittware IA-420f)
    # 5 = OFS PMCI boot controller (Silicom N6010) or OFS SPI boot controller (Silicom N5014)

    # BOOT component
    set boot_active_serial 0
    if {$BOOT_TYPE == 1 || $BOOT_TYPE == 2 || $BOOT_TYPE == 3} {
        append ret "boot:" [dts_boot_controller $ADDR_BOOT_CTRL $BOOT_TYPE]
    }
    if {$BOOT_TYPE == 4} {
        # ASx4 BOOT via Intel SDM client
        set boot_active_serial 1
    }
    if {$BOOT_TYPE == 5} {
        # OFS PMCI BOOT component
        append ret "boot:" [dts_ofs_pmci $ADDR_BOOT_CTRL]
    }

    append ret [dts_mi_test_space "mi_test_space" $ADDR_TEST_SPACE]

    # Card specific components
    if { [llength [info procs dts_card_specific]] > 0 } {
        append ret [ dts_card_specific ]
    }
    
    # TSU component
    global TSU_ENABLE
    if {$TSU_ENABLE} {
        append ret "tsu:" [dts_tsugen $ADDR_TSU]
    }

    # DMA module
    global DMA_TYPE DMA_RX_CHANNELS DMA_TX_CHANNELS PCIE_ENDPOINTS DMA_RX_FRAME_SIZE_MAX DMA_TX_FRAME_SIZE_MAX DMA_RX_FRAME_SIZE_MIN DMA_TX_FRAME_SIZE_MIN
    if {$DMA_TYPE != 0} {
        append ret [dts_dmamod_open $ADDR_DMA_MOD $DMA_TYPE [expr $DMA_RX_CHANNELS / $PCIE_ENDPOINTS] [expr $DMA_TX_CHANNELS / $PCIE_ENDPOINTS] $mi_idx $DMA_RX_FRAME_SIZE_MAX $DMA_TX_FRAME_SIZE_MAX $DMA_RX_FRAME_SIZE_MIN $DMA_TX_FRAME_SIZE_MIN]
    }

    global DMA_DEBUG_ENABLE
    if {$DMA_TYPE == 4 && $DMA_DEBUG_ENABLE} {
        append ret [data_logger "0x1320000" 0 "dma_calypte_latency_meter"]
    }

    # Network module
    global NET_MOD_ARCH ETH_PORTS ETH_PORT_SPEED ETH_PORT_CHAN ETH_PORT_LANES ETH_PORT_RX_MTU ETH_PORT_TX_MTU NET_MOD_ARCH QSFP_CAGES QSFP_I2C_ADDR
    if {$NET_MOD_ARCH != "EMPTY"} {
        append ret [dts_network_mod $ADDR_ETH_MAC $ADDR_ETH_PCS $ADDR_ETH_PMD $ETH_PORTS ETH_PORT_SPEED ETH_PORT_CHAN ETH_PORT_LANES ETH_PORT_RX_MTU ETH_PORT_TX_MTU $NET_MOD_ARCH $QSFP_CAGES QSFP_I2C_ADDR $CARD_NAME]
    }

    global SDM_SYSMON_ARCH
    # Intel FPGA SDM controller
    if {$SDM_SYSMON_ARCH == "INTEL_SDM"} {
        append ret [dts_sdm_controller $ADDR_SDM_SYSMON $boot_active_serial]
    }
    # Deprecated ID component to access Xilinx SYSMON
    if {$SDM_SYSMON_ARCH == "USP_IDCOMP"} {
        append ret "idcomp:" [dts_idcomp $ADDR_SDM_SYSMON]
    }
    # Deprecated Intel Stratix 10 ADC Sensor Component
    if {$SDM_SYSMON_ARCH == "S10_ADC"} {
        append ret [dts_stratix_adc_sensors $ADDR_SDM_SYSMON]
    }

    global CLOCK_GEN_ARCH VIRTUAL_DEBUG_ENABLE
    # Intel JTAG-over-protocol controller
    if {$CLOCK_GEN_ARCH == "INTEL" && $VIRTUAL_DEBUG_ENABLE} {
        append ret [dts_jtag_op_controller $ADDR_JTAG_IP]
    }

    # Populate application, if exists
    global APP_CORE_ENABLE
    if {$APP_CORE_ENABLE} {
        if { [llength [info procs dts_application]] > 0 } {
            global MEM_PORTS HBM_PORTS

            if {[llength [info args dts_application]] == 3} {
                # INFO: backward compatible variant without generics parameter
                append ret "app:" [dts_application $ADDR_USERAPP $ETH_PORTS $MEM_PORTS]
            } else {
                array set GENERICS "
                    ETH_STREAMS $ETH_PORTS
                    DDR_PORTS $MEM_PORTS
                    HBM_PORTS $HBM_PORTS
                "
                append ret "app:" [dts_application $ADDR_USERAPP [array get GENERICS]]
            }
        }
    }

    # Gen Loop Switch debug modules for each DMA stream/module
    global DMA_MODULES
    for {set i 0} {$i < $DMA_MODULES} {incr i} {
        set    gls_offset [expr $i * 0x200]
        append ret [dts_gen_loop_switch [expr $ADDR_GEN_LOOP + $gls_offset] "dbg_gls$i"]
    }

    # PCIe Debug
    global PCIE_CORE_DEBUG_ENABLE PCIE_CTRL_DEBUG_ENABLE PCIE_ENDPOINT_MODE PCIE_MOD_ARCH
    if {$PCIE_CORE_DEBUG_ENABLE} {
        append ret [dts_pcie_core_dbg $ADDR_PCIE_DBG $PCIE_ENDPOINTS $PCIE_ENDPOINT_MODE $PCIE_MOD_ARCH]
    }
    if {$PCIE_CTRL_DEBUG_ENABLE} {
        set pcie_ctrl_base [expr $ADDR_PCIE_DBG + "0x100000"]
        append ret [dts_pcie_ctrl_dbg $pcie_ctrl_base $PCIE_ENDPOINTS $PCIE_ENDPOINT_MODE $PCIE_MOD_ARCH]
    }

    append ret "};"

    set mi_idx [incr mi_idx]

    # Creating separate space for MI bus when DMA Calypte are used, the core uses additional BAR for its function
    if {$DMA_TYPE == 4 && $DMA_TX_CHANNELS > 0} {
        append ret "mi$mi_idx: mi_bus$mi_idx {"
        append ret "#address-cells = <1>;"
        append ret "#size-cells = <1>;"

        append ret "compatible = \"netcope,bus,mi\";"
        append ret "resource = \"PCI0,BAR2\";"
        append ret "width = <0x20>;"
        append ret "map-as-wc;"

        set mi_idx [incr mi_idx]

        # -------------------------------------------------
        # These two widths are changeable
        # -------------------------------------------------
        global DMA_TX_DATA_PTR_W
        set DATA_PTR_W   $DMA_TX_DATA_PTR_W
        set HDR_PTR_W    [expr $DATA_PTR_W - 3]

        # -------------------------------------------------
        # The following parts should not be changed
        # -------------------------------------------------

        if {$DATA_PTR_W < $HDR_PTR_W} {
            error "Header pointer width ($HDR_PTR_W) is greater that the width of the data pointer ($DATA_PTR_W)!
            This does not make sense since there would be more packets possible than there are bytes available
            in the data buffer"
        }
        set DATA_ADDR_W $DATA_PTR_W
        set HDR_ADDR_W  [expr $HDR_PTR_W + 3]

        set CHAN_PER_EP [expr $DMA_TX_CHANNELS / $PCIE_ENDPOINTS]

        # Calculation of the addres range reserved for single channel
        set TX_DATA_BUFF_BASE       "0x00000000"
        set TX_BUFF_SIZE       [expr int(pow(2,max($DATA_ADDR_W, $HDR_ADDR_W))) * 2]
        set TX_BUFF_SIZE_HEX   [format "0x%x" $TX_BUFF_SIZE]

        for {set i 0} {$i < $CHAN_PER_EP} {incr i} {
            set    var_buff_base [expr $TX_DATA_BUFF_BASE + $i * $TX_BUFF_SIZE_HEX]
            append ret [dts_dma_calypte_tx_buffer "data" $i $var_buff_base $TX_BUFF_SIZE_HEX "0"]
        }

        set TX_HDR_BUFF_BASE   [expr $TX_DATA_BUFF_BASE + $CHAN_PER_EP*$TX_BUFF_SIZE]
        set TX_BUFF_SIZE_HEX   [format "0x%x" $TX_BUFF_SIZE]

        for {set i 0} {$i < $CHAN_PER_EP} {incr i} {
            set    var_buff_base [expr $TX_HDR_BUFF_BASE + $i * $TX_BUFF_SIZE_HEX]
            append ret [dts_dma_calypte_tx_buffer "hdr" $i $var_buff_base $TX_BUFF_SIZE_HEX "0"]
        }
        append ret "};"
    }

    for {set i $mi_idx} {$i < $PCIE_ENDPOINTS} {incr i} {
        # Create MI bus node
        append ret "mi$i: mi_bus$i {"
        append ret "#address-cells = <1>;"
        append ret "#size-cells = <1>;"

        append ret "compatible = \"netcope,bus,mi\";"
        append ret "resource = \"PCI$i,BAR0\";"
        append ret "width = <0x20>;"

        if {$DMA_TYPE != 0} {
            append ret [dts_dmamod_open $ADDR_DMA_MOD $DMA_TYPE [expr $DMA_RX_CHANNELS / $PCIE_ENDPOINTS] [expr $DMA_TX_CHANNELS / $PCIE_ENDPOINTS] $i $DMA_RX_FRAME_SIZE_MAX $DMA_TX_FRAME_SIZE_MAX $DMA_RX_FRAME_SIZE_MIN $DMA_TX_FRAME_SIZE_MIN]
        }
        append ret "};"
    }

    return $ret
}
