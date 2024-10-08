# dts_dma_calypte_ctrl parameters:
# 1. dir        - direction which to choose (rx or tx)
# 2. id         - channel ID
# 3. base       - base address of channel
# 4. pcie       - index(es) of PCIe endpoint(s) which DMA controller uses.
proc dts_dma_calypte_ctrl {dir id base pcie} {
    set    ret ""
    append ret "dma_ctrl_calypte" "_$dir$id {"
    append ret "compatible = \"cesnet,dma_ctrl_calypte" "_" $dir "\";"
    append ret "reg = <$base 0x80>;"
    append ret "version = <0x00010000>;"
    append ret "pcie = <$pcie>;"
    if { $dir == "tx" } {
        append ret "data_buff = <&dma_calypte_tx_data_buff$id>;"
        append ret "hdr_buff = <&dma_calypte_tx_hdr_buff$id>;"
    }
    append ret "params = <&dma_params_$dir$pcie>;"
    append ret "};"
    return $ret
}

# generates Device Tree entries for data buffers in DMA Calypte
# 1. type       - content of the buffer (header or data)
# 2. id         - channel ID
# 3. base       - base address for the first buffer
# 4. size       - size of the buffer
# 5. pcie       - index(es) of PCIe endpoint(s) which DMA controller uses.
proc dts_dma_calypte_tx_buffer {type id base size pcie} {
    set ret ""
    append ret "dma_calypte_tx_${type}_buff${id}: dma_calypte_tx_${type}_buff${id} {"
    append ret "compatible = \"cesnet,dma_calypte_tx_${type}_buff\";"
    append ret "reg = <$base $size>;"
    append ret "pcie = <$pcie>;"
    append ret "};"
    return $ret
}
