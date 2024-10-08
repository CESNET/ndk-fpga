-- dma_hdr_pkg.vhd: Provides constants for the DMA/PCIex headers used in the LL DMA design.
-- Copyright (c) 2022 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-CLause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

package dma_hdr_pkg is

    --=============================================================================================================
    -- DMA header parameters widths
    --=============================================================================================================
    constant DMA_FRAME_LENGTH_W : natural := 16;
    constant DMA_FRAME_PTR_W    : natural := 16;
    constant DMA_VLD_BIT_W      : natural := 1;
    constant DMA_RSVD_BITS_W    : natural := 7;
    constant DMA_USR_METADATA_W : natural := 24;
    --=============================================================================================================


    --=============================================================================================================
    -- PCIe header parameters widths
    --=============================================================================================================
    constant PCIE_HDR_ADDR_TYPE_W       : natural := 2;
    constant PCIE_HDR_ADDR_W            : natural := 62;
    constant PCIE_HDR_DW_COUNT_W        : natural := 11;
    constant PCIE_HDR_REQ_TYPE_W        : natural := 4;
    constant PCIE_HDR_POI_REQ_W         : natural := 1;
    constant PCIE_HDR_REQ_ID_DEV_FUN_W  : natural := 8;
    constant PCIE_HDR_REQ_ID_BUS_W      : natural := 8;
    constant PCIE_HDR_TAG_W             : natural := 8;
    constant PCIE_HDR_COMP_ID_DEV_FUN_W : natural := 8;
    constant PCIE_HDR_COMP_ID_BUS_W     : natural := 8;
    constant PCIE_HDR_RQ_ID_ENA_W       : natural := 1;
    constant PCIE_HDR_TRANS_CLASS_W     : natural := 3;
    constant PCIE_HDR_ATTRIB_W          : natural := 3;
    constant PCIE_HDR_FRC_ECRC_W        : natural := 1;
    --=============================================================================================================


    --=============================================================================================================
    -- DMA header offsets
    --=============================================================================================================
    constant DMA_FRAME_LENGTH_O : natural := 0;
    constant DMA_FRAME_PTR_O    : natural := DMA_FRAME_LENGTH_O + DMA_FRAME_LENGTH_W;
    constant DMA_VLD_BIT_O      : natural := DMA_FRAME_PTR_O    + DMA_FRAME_PTR_W;
    constant DMA_RSVD_BITS_O    : natural := DMA_VLD_BIT_O      + DMA_VLD_BIT_W;
    constant DMA_USR_METADATA_O : natural := DMA_RSVD_BITS_O    + DMA_RSVD_BITS_W;
    --=============================================================================================================


    --=============================================================================================================
    -- PCIe header offsets
    --=============================================================================================================
    constant PCIE_HDR_ADDR_TYPE_O       : natural := 0;
    constant PCIE_HDR_ADDR_O            : natural := PCIE_HDR_ADDR_TYPE_O       + PCIE_HDR_ADDR_TYPE_W;
    constant PCIE_HDR_DW_COUNT_O        : natural := PCIE_HDR_ADDR_O            + PCIE_HDR_ADDR_W;
    constant PCIE_HDR_REQ_TYPE_O        : natural := PCIE_HDR_DW_COUNT_O        + PCIE_HDR_DW_COUNT_W;
    constant PCIE_HDR_POI_REQ_O         : natural := PCIE_HDR_REQ_TYPE_O        + PCIE_HDR_REQ_TYPE_W;
    constant PCIE_HDR_REQ_ID_DEV_FUN_O  : natural := PCIE_HDR_POI_REQ_O         + PCIE_HDR_POI_REQ_W;
    constant PCIE_HDR_REQ_ID_BUS_O      : natural := PCIE_HDR_REQ_ID_DEV_FUN_O  + PCIE_HDR_REQ_ID_DEV_FUN_W;
    constant PCIE_HDR_TAG_O             : natural := PCIE_HDR_REQ_ID_BUS_O      + PCIE_HDR_REQ_ID_BUS_W;
    constant PCIE_HDR_COMP_ID_DEV_FUN_O : natural := PCIE_HDR_TAG_O             + PCIE_HDR_TAG_W;
    constant PCIE_HDR_COMP_ID_BUS_O     : natural := PCIE_HDR_COMP_ID_DEV_FUN_O + PCIE_HDR_COMP_ID_DEV_FUN_W;
    constant PCIE_HDR_RQ_ID_ENA_O       : natural := PCIE_HDR_COMP_ID_BUS_O     + PCIE_HDR_COMP_ID_BUS_W;
    constant PCIE_HDR_TRANS_CLASS_O     : natural := PCIE_HDR_RQ_ID_ENA_O       + PCIE_HDR_RQ_ID_ENA_W;
    constant PCIE_HDR_ATTRIB_O          : natural := PCIE_HDR_TRANS_CLASS_O     + PCIE_HDR_TRANS_CLASS_W;
    constant PCIE_HDR_FRC_ECRC_O        : natural := PCIE_HDR_ATTRIB_O          + PCIE_HDR_ATTRIB_W;
    --=============================================================================================================


    --=============================================================================================================
    -- DMA header range specifications
    --=============================================================================================================
    subtype DMA_FRAME_LENGTH    is natural range DMA_FRAME_LENGTH_O + DMA_FRAME_LENGTH_W    - 1 downto DMA_FRAME_LENGTH_O;
    subtype DMA_FRAME_PTR       is natural range DMA_FRAME_PTR_O    + DMA_FRAME_PTR_W       - 1 downto DMA_FRAME_PTR_O;
    subtype DMA_VLD_BIT         is natural range DMA_VLD_BIT_O      + DMA_VLD_BIT_W         - 1 downto DMA_VLD_BIT_O;
    subtype DMA_RSVD_BITS       is natural range DMA_RSVD_BITS_O    + DMA_RSVD_BITS_W       - 1 downto DMA_RSVD_BITS_O;
    subtype DMA_USR_METADATA    is natural range DMA_USR_METADATA_O + DMA_USR_METADATA_W    - 1 downto DMA_USR_METADATA_O;
    --=============================================================================================================


    --=============================================================================================================
    -- PCIE header range specifications
    --=============================================================================================================
    subtype PCIE_HDR_ADDR_TYPE          is natural range PCIE_HDR_ADDR_TYPE_O       + PCIE_HDR_ADDR_TYPE_W          - 1 downto PCIE_HDR_ADDR_TYPE_O;
    subtype PCIE_HDR_ADDR               is natural range PCIE_HDR_ADDR_O            + PCIE_HDR_ADDR_W               - 1 downto PCIE_HDR_ADDR_O;
    subtype PCIE_HDR_DW_COUNT           is natural range PCIE_HDR_DW_COUNT_O        + PCIE_HDR_DW_COUNT_W           - 1 downto PCIE_HDR_DW_COUNT_O;
    subtype PCIE_HDR_REQ_TYPE           is natural range PCIE_HDR_REQ_TYPE_O        + PCIE_HDR_REQ_TYPE_W           - 1 downto PCIE_HDR_REQ_TYPE_O;
    subtype PCIE_HDR_POI_REQ            is natural range PCIE_HDR_POI_REQ_O         + PCIE_HDR_POI_REQ_W            - 1 downto PCIE_HDR_POI_REQ_O;
    subtype PCIE_HDR_REQ_ID_DEV_FUN     is natural range PCIE_HDR_REQ_ID_DEV_FUN_O  + PCIE_HDR_REQ_ID_DEV_FUN_W     - 1 downto PCIE_HDR_REQ_ID_DEV_FUN_O;
    subtype PCIE_HDR_REQ_ID_BUS         is natural range PCIE_HDR_REQ_ID_BUS_O      + PCIE_HDR_REQ_ID_BUS_W         - 1 downto PCIE_HDR_REQ_ID_BUS_O;
    subtype PCIE_HDR_TAG                is natural range PCIE_HDR_TAG_O             + PCIE_HDR_TAG_W                - 1 downto PCIE_HDR_TAG_O;
    subtype PCIE_HDR_COMP_ID_DEV_FUN    is natural range PCIE_HDR_COMP_ID_DEV_FUN_O + PCIE_HDR_COMP_ID_DEV_FUN_W    - 1 downto PCIE_HDR_COMP_ID_DEV_FUN_O;
    subtype PCIE_HDR_COMP_ID_BUS        is natural range PCIE_HDR_COMP_ID_BUS_O     + PCIE_HDR_COMP_ID_BUS_W        - 1 downto PCIE_HDR_COMP_ID_BUS_O;
    subtype PCIE_HDR_RQ_ID_ENA          is natural range PCIE_HDR_RQ_ID_ENA_O       + PCIE_HDR_RQ_ID_ENA_W          - 1 downto PCIE_HDR_RQ_ID_ENA_O;
    subtype PCIE_HDR_TRANS_CLASS        is natural range PCIE_HDR_TRANS_CLASS_O     + PCIE_HDR_TRANS_CLASS_W        - 1 downto PCIE_HDR_TRANS_CLASS_O;
    subtype PCIE_HDR_ATTRIB             is natural range PCIE_HDR_ATTRIB_O          + PCIE_HDR_ATTRIB_W             - 1 downto PCIE_HDR_ATTRIB_O;
    subtype PCIE_HDR_FRC_ECRC           is natural range PCIE_HDR_FRC_ECRC_O        + PCIE_HDR_FRC_ECRC_W           - 1 downto PCIE_HDR_FRC_ECRC_O;
    --=============================================================================================================


    constant DMA_HDR_WIDTH : natural := 64;
    -- Lengths of two variants of the PCIe header
    constant PCIE_BIG_UPHDR_WIDTH   : natural := 128;
    constant PCIE_SMALL_UPHDR_WIDTH : natural := 96;

    constant PCIE_HDR_BIG   : std_logic := '1';
    constant PCIE_HDR_SMALL : std_logic := '0';

end package;

package body dma_hdr_pkg is

end package body;
