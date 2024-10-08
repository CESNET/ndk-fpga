// pcie_meta_pack.sv: PCIe MFB Meta Package
// Copyright (C) 2022 CESNET
// Author: Daniel Kriz <danielkriz@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

// -----------------------------------------------------------------------------
// PCIe MFB Meta Package
// -----------------------------------------------------------------------------

// **PCIe CQ MFB Meta items description:**
//
// ============== ============ =================================================
// Item bit range Item name    Item description
// ============== ============ =================================================
// 0   to 127     HEADER       TLP header - Intel FPGA (P-Tile, R-Tile) only
// 128 to 159     PREFIX       TLP prefix - Intel FPGA (P-Tile, R-Tile) only
// 160 to 162     BAR          BAR index - Intel FPGA only
// 163 to 166     FBE          First Byte Enable - Xilinx FPGA only
// 167 to 170     LBE          Last Byte Enable - Xilinx FPGA only
// 171 to 171     TPH_PRESENT  Transaction Processing Hint (TPH) present flag - Xilinx FPGA only
// 172 to 173     TPH_TYPE     The PH field associated with the hint - Xilinx FPGA only
// 174 to 181     TPH_ST_TAG   The Steering Tag associated with the hint - Xilinx FPGA only
// ============== ============ =================================================
//
// **PCIe CC MFB Meta items description:**
//
// ============== ============ =================================================
// Item bit range Item name    Item description
// ============== ============ =================================================
// 0  to 95       HEADER       TLP header - Intel FPGA (P-Tile, R-Tile) only
// 96 to 127      PREFIX       TLP prefix - Intel FPGA (P-Tile, R-Tile) only
// ============== ============ =================================================
//
// **PCIe RQ MFB Meta items description:**
//
// ============== ============ =================================================
// Item bit range Item name    Item description
// ============== ============ =================================================
// 0   to 127     HEADER       TLP header - Intel FPGA (P-Tile, R-Tile) only
// 128 to 159     PREFIX       TLP prefix - Intel FPGA (P-Tile, R-Tile) only
// 160 to 163     FBE          First Byte Enable - Xilinx FPGA only
// 164 to 167     LBE          Last Byte Enable - Xilinx FPGA only
// ============== ============ =================================================
//
// **PCIe RC MFB Meta items description:**
//
// ============== ============ =================================================
// Item bit range Item name    Item description
// ============== ============ =================================================
// 0  to 95       HEADER       TLP header - Intel FPGA (P-Tile, R-Tile) only
// 96 to 127      PREFIX       TLP prefix - Intel FPGA (P-Tile, R-Tile) only
// ============== ============ =================================================
package sv_pcie_meta_pack;

    parameter PCIE_META_REQ_HDR_W     = 128;
    parameter PCIE_META_CPL_HDR_W     = 96;
    parameter PCIE_META_PREFIX_W      = 32;
    parameter PCIE_META_BAR_W         = 3;
    parameter PCIE_META_FBE_W         = 4;
    parameter PCIE_META_LBE_W         = 4;
    parameter PCIE_META_TPH_PRESENT_W = 1;
    parameter PCIE_META_TPH_TYPE_W    = 2;
    parameter PCIE_META_TPH_ST_TAG_W  = 8;

    parameter PCIE_RC_META_HEADER_O = 0;
    parameter PCIE_RC_META_PREFIX_O = PCIE_RC_META_HEADER_O + PCIE_META_CPL_HDR_W;

    parameter PCIE_RC_META_WIDTH    = PCIE_RC_META_PREFIX_O + PCIE_META_PREFIX_W;

    parameter PCIE_RQ_META_HEADER_O = 0;
    parameter PCIE_RQ_META_PREFIX_O = PCIE_RQ_META_HEADER_O + PCIE_META_REQ_HDR_W;
    parameter PCIE_RQ_META_FBE_O    = PCIE_RQ_META_PREFIX_O + PCIE_META_PREFIX_W;
    parameter PCIE_RQ_META_LBE_O    = PCIE_RQ_META_FBE_O    + PCIE_META_FBE_W;

    parameter PCIE_RQ_META_WIDTH    = PCIE_RQ_META_LBE_O + PCIE_META_LBE_W;

    parameter PCIE_CQ_META_HEADER_O      = 0;
    parameter PCIE_CQ_META_PREFIX_O      = PCIE_CQ_META_HEADER_O      + PCIE_META_REQ_HDR_W;
    parameter PCIE_CQ_META_BAR_O         = PCIE_CQ_META_PREFIX_O      + PCIE_META_PREFIX_W;
    parameter PCIE_CQ_META_FBE_O         = PCIE_CQ_META_BAR_O         + PCIE_META_BAR_W;
    parameter PCIE_CQ_META_LBE_O         = PCIE_CQ_META_FBE_O         + PCIE_META_FBE_W;
    parameter PCIE_CQ_META_TPH_PRESENT_O = PCIE_CQ_META_LBE_O         + PCIE_META_LBE_W;
    parameter PCIE_CQ_META_TPH_TYPE_O    = PCIE_CQ_META_TPH_PRESENT_O + PCIE_META_TPH_PRESENT_W;
    parameter PCIE_CQ_META_TPH_ST_TAG_O  = PCIE_CQ_META_TPH_TYPE_O    + PCIE_META_TPH_TYPE_W;

    parameter PCIE_CQ_META_WIDTH         = PCIE_CQ_META_TPH_ST_TAG_O + PCIE_META_TPH_ST_TAG_W;

    parameter PCIE_CC_META_HEADER_O = 0;
    parameter PCIE_CC_META_PREFIX_O = PCIE_CC_META_HEADER_O + PCIE_META_CPL_HDR_W;

    parameter PCIE_CC_META_WIDTH    = PCIE_CC_META_PREFIX_O + PCIE_META_PREFIX_W;

endpackage
