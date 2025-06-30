namespace eval NdkCore {
    # =========================================================================
    # MI ADDRESS SPACE
    # Changes must also be made manually in VHDL package:
    # <NDK-CORE_root_directory>/intel/src/mi_addr_space_pkg.vhd
    # =========================================================================
    set ADDR_TEST_SPACE "0x00000000"
    set ADDR_FREQ_METER "0x00000800"
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
}

proc dts_ndk_core_info {DTS} {
    upvar 1 $DTS ret

    global CARD_NAME DT_PROJECT_TEXT PROJECT_VARIANT PROJECT_VERSION

    dts_appendprop_string ret "card-name" "$CARD_NAME"
    if {[info exists DT_PROJECT_TEXT]} {
        dts_appendprop_string ret "project-name" "$DT_PROJECT_TEXT"
    }
    if {[info exists PROJECT_VARIANT]} {
        dts_appendprop_string ret "project-variant" "$PROJECT_VARIANT"
    }
    if {[info exists PROJECT_VERSION]} {
        dts_appendprop_string ret "project-version" "$PROJECT_VERSION"
    }
}

proc dts_ndk_core_boot_module {DTS} {
    upvar 1 $DTS ret

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
        append ret "boot:" [dts_boot_controller $NdkCore::ADDR_BOOT_CTRL $BOOT_TYPE]
    }
    if {$BOOT_TYPE == 4} {
        # ASx4 BOOT via Intel SDM client
        set boot_active_serial 1
    }
    if {$BOOT_TYPE == 5} {
        # OFS PMCI BOOT component
        append ret "boot:" [dts_ofs_pmci $NdkCore::ADDR_BOOT_CTRL]
    }

    global SDM_SYSMON_ARCH
    # Intel FPGA SDM controller
    if {$SDM_SYSMON_ARCH == "INTEL_SDM"} {
        append ret [dts_sdm_controller $NdkCore::ADDR_SDM_SYSMON $boot_active_serial]
    # Deprecated ID component to access Xilinx SYSMON
    } elseif {$SDM_SYSMON_ARCH == "USP_IDCOMP"} {
        append ret "idcomp:" [dts_idcomp $NdkCore::ADDR_SDM_SYSMON]
    # Deprecated Intel Stratix 10 ADC Sensor Component
    } elseif {$SDM_SYSMON_ARCH == "S10_ADC"} {
        append ret [dts_stratix_adc_sensors $NdkCore::ADDR_SDM_SYSMON]
    }
}

proc dts_ndp_core_main_mi {DTS} {
    upvar 1 $DTS ret

    # Boot module
    dts_ndk_core_boot_module ret

    # MI test space
    append ret [dts_mi_test_space "mi_test_space" $NdkCore::ADDR_TEST_SPACE]

    # Frequency meter component
    global MEASURE_FREQUENCIES
    if {$MEASURE_FREQUENCIES} {
        append ret [dts_frequency_counter $NdkCore::ADDR_FREQ_METER]
    }

    # Card specific components
    if { [llength [info procs dts_card_specific]] > 0 } {
        set cs_args [info args dts_card_specific]
        lappend cs_params
        if {[llength cs_args] > 0} {
            lappend cs_params $NdkCore::ADDR_BOOT_CTRL
        }
        append ret [dts_card_specific {*}$cs_params]
    }

    # TSU component
    global TSU_ENABLE
    if {$TSU_ENABLE} {
        append ret "tsu:" [dts_tsugen $NdkCore::ADDR_TSU]
    }

    # Network module
    global NET_MOD_ARCH ETH_PORTS ETH_PORT_SPEED ETH_PORT_CHAN ETH_PORT_LANES ETH_PORT_RX_MTU ETH_PORT_TX_MTU NET_MOD_ARCH QSFP_CAGES QSFP_I2C_ADDR QSFP_I2C_CUSTOM_CTRLS CARD_NAME
    if {$NET_MOD_ARCH != "EMPTY"} {
        append ret [dts_network_mod $NdkCore::ADDR_ETH_MAC $NdkCore::ADDR_ETH_PCS $NdkCore::ADDR_ETH_PMD $ETH_PORTS ETH_PORT_SPEED ETH_PORT_CHAN ETH_PORT_LANES ETH_PORT_RX_MTU ETH_PORT_TX_MTU $NET_MOD_ARCH $QSFP_CAGES QSFP_I2C_ADDR $CARD_NAME $QSFP_I2C_CUSTOM_CTRLS]
    }

    global CLOCK_GEN_ARCH VIRTUAL_DEBUG_ENABLE
    # Intel JTAG-over-protocol controller
    if {$CLOCK_GEN_ARCH == "INTEL" && $VIRTUAL_DEBUG_ENABLE} {
        append ret [dts_jtag_op_controller $NdkCore::ADDR_JTAG_IP]
    }

    # Populate application, if exists
    global APP_CORE_ENABLE
    global ETH_STREAMS_MODE
    if {$ETH_STREAMS_MODE == 1} {
        set ETH_STREAMS [expr $ETH_PORTS*$ETH_PORT_CHAN(0)]
    } else {
        set ETH_STREAMS $ETH_PORTS
    }
    if {$APP_CORE_ENABLE} {
        if { [llength [info procs dts_application]] > 0 } {
            global MEM_PORTS HBM_PORTS

            if {[llength [info args dts_application]] == 3} {
                # INFO: backward compatible variant without generics parameter
                append ret "app:" [dts_application $NdkCore::ADDR_USERAPP $ETH_STREAMS $MEM_PORTS]
            } else {
                array set GENERICS "
                    ETH_STREAMS $ETH_STREAMS
                    DDR_PORTS $MEM_PORTS
                    HBM_PORTS $HBM_PORTS
                "
                append ret "app:" [dts_application $NdkCore::ADDR_USERAPP [array get GENERICS]]
            }
        }
    }

    # Gen Loop Switch debug modules for each DMA stream/module
    global DMA_MODULES DMA_GEN_LOOP_EN
    if {$DMA_GEN_LOOP_EN} {
        for {set i 0} {$i < $DMA_MODULES} {incr i} {
            set    gls_offset [expr $i * 0x200]
            append ret [dts_gen_loop_switch [expr $NdkCore::ADDR_GEN_LOOP + $gls_offset] "dbg_gls$i"]
        }
    }

    # PCIe Debug
    global PCIE_ENDPOINTS PCIE_CORE_DEBUG_ENABLE PCIE_CTRL_DEBUG_ENABLE PCIE_ENDPOINT_MODE PCIE_MOD_ARCH
    if {$PCIE_CORE_DEBUG_ENABLE} {
        append ret [dts_pcie_core_dbg $NdkCore::ADDR_PCIE_DBG $PCIE_ENDPOINTS $PCIE_ENDPOINT_MODE $PCIE_MOD_ARCH]
    }
    if {$PCIE_CTRL_DEBUG_ENABLE} {
        set pcie_ctrl_base [expr $NdkCore::ADDR_PCIE_DBG + "0x100000"]
        append ret [dts_pcie_ctrl_dbg $pcie_ctrl_base $PCIE_ENDPOINTS $PCIE_ENDPOINT_MODE $PCIE_MOD_ARCH]
    }
}

proc dts_ndk_core_dma_calypte_tx_buffers {DTS PCIE_ENDPOINTS DMA_TX_CHANNELS} {
    upvar 1 $DTS ret

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
            dts_dma_calypte_tx_buffer ret "data" $i $var_buff_base $TX_BUFF_SIZE_HEX "0"
        }

        set TX_HDR_BUFF_BASE   [expr $TX_DATA_BUFF_BASE + $CHAN_PER_EP*$TX_BUFF_SIZE]
        set TX_BUFF_SIZE_HEX   [format "0x%x" $TX_BUFF_SIZE]

        for {set i 0} {$i < $CHAN_PER_EP} {incr i} {
            set    var_buff_base [expr $TX_HDR_BUFF_BASE + $i * $TX_BUFF_SIZE_HEX]
            dts_dma_calypte_tx_buffer ret "hdr" $i $var_buff_base $TX_BUFF_SIZE_HEX "0"
        }
}

proc dts_build_netcope {} {
    # =========================================================================
    # Top level Device tree file
    # =========================================================================

    set ret ""

    dts_ndk_core_info ret

    # Create MI bus nodes for each PCIe endpoint
    global PCIE_ENDPOINTS DMA_TYPE DMA_TX_CHANNELS
    foreach pcie [nb_range $PCIE_ENDPOINTS] {
        dts_create_default_mi_bar_node ret $pcie 0 {
            if {$pcie == 0} {
                dts_ndp_core_main_mi ret
            }

            # DMA module
            global DMA_RX_CHANNELS DMA_RX_FRAME_SIZE_MAX DMA_TX_FRAME_SIZE_MAX DMA_RX_FRAME_SIZE_MIN DMA_TX_FRAME_SIZE_MIN DMA_DEBUG_ENABLE
            if {$DMA_TYPE != 0} {
                append ret [dts_dmamod_open $NdkCore::ADDR_DMA_MOD $DMA_TYPE [expr $DMA_RX_CHANNELS / $PCIE_ENDPOINTS] [expr $DMA_TX_CHANNELS / $PCIE_ENDPOINTS] $pcie $DMA_RX_FRAME_SIZE_MAX $DMA_TX_FRAME_SIZE_MAX $DMA_RX_FRAME_SIZE_MIN $DMA_TX_FRAME_SIZE_MIN $DMA_DEBUG_ENABLE]
            }
        }

        dts_create_default_mi_bar_node ret $pcie 2 {
            append ret "map-as-wc;"
            # Creating separate space for MI bus when DMA Calypte are used, the core uses additional BAR for its function
            if {$DMA_TYPE == 4} {
                dts_ndk_core_dma_calypte_tx_buffers ret $PCIE_ENDPOINTS $DMA_TX_CHANNELS
            }
        }
    }

    return $ret
}
