-- pcie_meta_pack.vhd: PCIe MFB Meta Package
-- Copyright (C) 2022 CESNET
-- Author: Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

-- -----------------------------------------------------------------------------
-- PCIe MFB Meta Package
-- -----------------------------------------------------------------------------

-- **PCIe CQ MFB Meta items description:**
--
-- ============== ============ =================================================
-- Item bit range Item name    Item description
-- ============== ============ =================================================
-- 0   to 127     HEADER       TLP header - Intel FPGA (P-Tile, R-Tile) only
-- 128 to 159     PREFIX       TLP prefix - Intel FPGA (P-Tile, R-Tile) only
-- 160 to 162     BAR          BAR index - Intel FPGA only
-- 163 to 166     FBE          First Byte Enable - Xilinx FPGA only
-- 167 to 170     LBE          Last Byte Enable - Xilinx FPGA only
-- 171 to 171     TPH_PRESENT  Transaction Processing Hint (TPH) present flag - Xilinx FPGA only
-- 172 to 173     TPH_TYPE     The PH field associated with the hint - Xilinx FPGA only
-- 174 to 181     TPH_ST_TAG   The Steering Tag associated with the hint - Xilinx FPGA only
-- ============== ============ =================================================
--
-- **PCIe CC MFB Meta items description:**
--
-- ============== ============ =================================================
-- Item bit range Item name    Item description
-- ============== ============ =================================================
-- 0  to 95       HEADER       TLP header - Intel FPGA (P-Tile, R-Tile) only
-- 96 to 127      PREFIX       TLP prefix - Intel FPGA (P-Tile, R-Tile) only
-- ============== ============ =================================================
--
-- **PCIe RQ MFB Meta items description:**
--
-- ============== ============ =================================================
-- Item bit range Item name    Item description
-- ============== ============ =================================================
-- 0   to 127     HEADER       TLP header - Intel FPGA (P-Tile, R-Tile) only
-- 128 to 159     PREFIX       TLP prefix - Intel FPGA (P-Tile, R-Tile) only
-- 160 to 163     FBE          First Byte Enable - Xilinx FPGA only
-- 164 to 167     LBE          Last Byte Enable - Xilinx FPGA only
-- ============== ============ =================================================
--
-- **PCIe RC MFB Meta items description:**
--
-- ============== ============ =================================================
-- Item bit range Item name    Item description
-- ============== ============ =================================================
-- 0  to 95       HEADER       TLP header - Intel FPGA (P-Tile, R-Tile) only
-- 96 to 127      PREFIX       TLP prefix - Intel FPGA (P-Tile, R-Tile) only
-- ============== ============ =================================================
package pcie_meta_pack is

    constant PCIE_META_REQ_HDR_W      : natural := 128;
    constant PCIE_META_CPL_HDR_W      : natural := 96;
    constant PCIE_META_PREFIX_W       : natural := 32;
    constant PCIE_META_BAR_W          : natural := 3;
    constant PCIE_META_FBE_W          : natural := 4;
    constant PCIE_META_LBE_W          : natural := 4;
    constant PCIE_META_TPH_PRESENT_W  : natural := 1;
    constant PCIE_META_TPH_TYPE_W     : natural := 2;
    constant PCIE_META_TPH_ST_TAG_W   : natural := 8;

    constant PCIE_RC_META_HEADER_O : natural := 0;
    constant PCIE_RC_META_PREFIX_O : natural := PCIE_RC_META_HEADER_O + PCIE_META_CPL_HDR_W;

    constant PCIE_RC_META_WIDTH    : natural := PCIE_RC_META_PREFIX_O + PCIE_META_PREFIX_W;

    subtype PCIE_RC_META_HEADER is natural range PCIE_RC_META_HEADER_O + PCIE_META_CPL_HDR_W -1 downto PCIE_RC_META_HEADER_O;
    subtype PCIE_RC_META_PREFIX is natural range PCIE_RC_META_PREFIX_O + PCIE_META_PREFIX_W  -1 downto PCIE_RC_META_PREFIX_O;

    constant PCIE_RQ_META_HEADER_O : natural := 0;
    constant PCIE_RQ_META_PREFIX_O : natural := PCIE_RQ_META_HEADER_O + PCIE_META_REQ_HDR_W;
    constant PCIE_RQ_META_FBE_O    : natural := PCIE_RQ_META_PREFIX_O + PCIE_META_PREFIX_W;
    constant PCIE_RQ_META_LBE_O    : natural := PCIE_RQ_META_FBE_O    + PCIE_META_FBE_W;

    constant PCIE_RQ_META_WIDTH    : natural := PCIE_RQ_META_LBE_O + PCIE_META_LBE_W;

    subtype PCIE_RQ_META_HEADER is natural range PCIE_RQ_META_HEADER_O + PCIE_META_REQ_HDR_W -1 downto PCIE_RQ_META_HEADER_O;
    subtype PCIE_RQ_META_PREFIX is natural range PCIE_RQ_META_PREFIX_O + PCIE_META_PREFIX_W  -1 downto PCIE_RQ_META_PREFIX_O;
    subtype PCIE_RQ_META_FBE    is natural range PCIE_RQ_META_FBE_O    + PCIE_META_FBE_W     -1 downto PCIE_RQ_META_FBE_O;
    subtype PCIE_RQ_META_LBE    is natural range PCIE_RQ_META_LBE_O    + PCIE_META_LBE_W     -1 downto PCIE_RQ_META_LBE_O;

    constant PCIE_CQ_META_HEADER_O      : natural := 0;
    constant PCIE_CQ_META_PREFIX_O      : natural := PCIE_CQ_META_HEADER_O      + PCIE_META_REQ_HDR_W;
    constant PCIE_CQ_META_BAR_O         : natural := PCIE_CQ_META_PREFIX_O      + PCIE_META_PREFIX_W;
    constant PCIE_CQ_META_FBE_O         : natural := PCIE_CQ_META_BAR_O         + PCIE_META_BAR_W;
    constant PCIE_CQ_META_LBE_O         : natural := PCIE_CQ_META_FBE_O         + PCIE_META_FBE_W;
    constant PCIE_CQ_META_TPH_PRESENT_O : natural := PCIE_CQ_META_LBE_O         + PCIE_META_LBE_W;
    constant PCIE_CQ_META_TPH_TYPE_O    : natural := PCIE_CQ_META_TPH_PRESENT_O + PCIE_META_TPH_PRESENT_W;
    constant PCIE_CQ_META_TPH_ST_TAG_O  : natural := PCIE_CQ_META_TPH_TYPE_O    + PCIE_META_TPH_TYPE_W;

    constant PCIE_CQ_META_WIDTH         : natural := PCIE_CQ_META_TPH_ST_TAG_O + PCIE_META_TPH_ST_TAG_W;

    subtype PCIE_CQ_META_HEADER      is natural range PCIE_CQ_META_HEADER_O      + PCIE_META_REQ_HDR_W     -1 downto PCIE_CQ_META_HEADER_O;
    subtype PCIE_CQ_META_PREFIX      is natural range PCIE_CQ_META_PREFIX_O      + PCIE_META_PREFIX_W      -1 downto PCIE_CQ_META_PREFIX_O;
    subtype PCIE_CQ_META_BAR         is natural range PCIE_CQ_META_BAR_O         + PCIE_META_BAR_W         -1 downto PCIE_CQ_META_BAR_O;
    subtype PCIE_CQ_META_FBE         is natural range PCIE_CQ_META_FBE_O         + PCIE_META_FBE_W         -1 downto PCIE_CQ_META_FBE_O;
    subtype PCIE_CQ_META_LBE         is natural range PCIE_CQ_META_LBE_O         + PCIE_META_LBE_W         -1 downto PCIE_CQ_META_LBE_O;
    subtype PCIE_CQ_META_TPH_PRESENT is natural range PCIE_CQ_META_TPH_PRESENT_O + PCIE_META_TPH_PRESENT_W -1 downto PCIE_CQ_META_TPH_PRESENT_O;
    subtype PCIE_CQ_META_TPH_TYPE    is natural range PCIE_CQ_META_TPH_TYPE_O    + PCIE_META_TPH_TYPE_W    -1 downto PCIE_CQ_META_TPH_TYPE_O;
    subtype PCIE_CQ_META_TPH_ST_TAG  is natural range PCIE_CQ_META_TPH_ST_TAG_O  + PCIE_META_TPH_ST_TAG_W  -1 downto PCIE_CQ_META_TPH_ST_TAG_O;

    constant PCIE_CC_META_HEADER_O : natural := 0;
    constant PCIE_CC_META_PREFIX_O : natural := PCIE_CC_META_HEADER_O + PCIE_META_CPL_HDR_W;

    constant PCIE_CC_META_WIDTH    : natural := PCIE_CC_META_PREFIX_O + PCIE_META_PREFIX_W;

    subtype PCIE_CC_META_HEADER is natural range PCIE_CC_META_HEADER_O + PCIE_META_CPL_HDR_W -1 downto PCIE_CC_META_HEADER_O;
    subtype PCIE_CC_META_PREFIX is natural range PCIE_CC_META_PREFIX_O + PCIE_META_PREFIX_W  -1 downto PCIE_CC_META_PREFIX_O;

end package;

-- -----------------------------------------------------------------------------
-- Package body
-- -----------------------------------------------------------------------------

package body pcie_meta_pack is

end package body;
