# Modules.tcl: Components include script
# Copyright (C) 2025 MAGMIO, a.s.
# Author(s): Vladislav Valek <vladislawalek@gmail.com>

lappend PACKAGES "$OFM_PATH/comp/base/pkg/math_pack.vhd"
lappend PACKAGEG "$OFM_PATH/comp/base/pkg/type_pack.vhd"
lappend PACKAGES "$OFM_PATH/comp/base/pkg/pcie_meta_pack.vhd"

set RQ_HDR_GEN_BASE  "$OFM_PATH/comp/pcie/others/hdr_gen/rq_hdr_gen"
set FIFOX_MULTI_BASE "$OFM_PATH/comp/base/fifo/fifox_multi"

lappend COMPONENTS [ list "PCIE_RQ_HDR_GEN" $RQ_HDR_GEN_BASE  "FULL"]
lappend COMPONENTS [ list "FIFOX_MULTI"     $FIFOX_MULTI_BASE "FULL"]

lappend MOD "$ENTITY_BASE/dma_ptr_updater.vhd"
