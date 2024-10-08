-- ptc_pcie2dma_hdr_transform_ent.vhd: PCIe to DMA header transform for PTC component - entity
-- Copyright (C) 2018 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>

-- SPDX-License-Identifier: BSD-3-Clause
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields

-- ----------------------------------------------------------------------------
--                             Entity
-- ----------------------------------------------------------------------------

entity PTC_PCIE2DMA_HDR_TRANSFORM is
generic(
    -- Number of MVB headers
    MVB_ITEMS          : integer := 2;

    -- Width of one PCIe UP header
    PCIE_DOWNHDR_WIDTH : integer := 3*4*8;

    -- Width of 'lower address' field in PCIE completion header
    -- 7 for Stratix10
    PCIE_LOW_ADDR_WIDTH : integer := 12;

    -- Width of DMA Tag field in MVB header (maximum defined by range in dma_bus_pack)
    DMA_TAG_WIDTH      : integer := DMA_REQUEST_TAG'high - DMA_REQUEST_TAG'low + 1;
    -- Width of DMA Unit ID field in MVB header (maximum defined by range in dma_bus_pack)
    DMA_ID_WIDTH       : integer := DMA_REQUEST_UNITID'high - DMA_REQUEST_UNITID'low + 1;

    -- Width of Tag field in PCIe header
    PCIE_TAG_WIDTH     : integer := 5;

    -- Target device
    -- "VIRTEX6", "7SERIES", "ULTRASCALE"
    DEVICE             : string  := "ULTRASCALE"
);
port(
    ---------------------------------------------------------------------------
    -- Common interface
    ---------------------------------------------------------------------------

    CLK                 : in  std_logic;
    RESET               : in  std_logic;

    ---------------------------------------------------------------------------
    -- RX PCIe MVB interface
    ---------------------------------------------------------------------------

    -- Upstream headers
    RX_MVB_DATA     : in  std_logic_vector(MVB_ITEMS*PCIE_DOWNHDR_WIDTH-1 downto 0);
    -- Valid bit for each UP header
    RX_MVB_VLD      : in  std_logic_vector(MVB_ITEMS                   -1 downto 0);
    -- Source ready entire UP stream
    RX_MVB_SRC_RDY  : in  std_logic;

    ---------------------------------------------------------------------------
    -- Interface to Tag manager for reverse mapping and releasing of tags
    ---------------------------------------------------------------------------

    -- PCIe tag of arriving completion transactions
    TAG                 : out std_logic_vector(MVB_ITEMS*PCIE_TAG_WIDTH-1 downto 0);
    -- Lower bits of address of requested tag's completition (address of a byte)
    TAG_COMPL_LOW_ADDR  : out std_logic_vector(MVB_ITEMS*PCIE_LOW_ADDR_WIDTH-1 downto 0);
    -- Length of requested tag's completition
    TAG_COMPL_LEN       : out std_logic_vector(MVB_ITEMS*(DMA_REQUEST_LENGTH'high-DMA_REQUEST_LENGTH'low+1)-1 downto 0);
    -- Order for reserved tag release
    TAG_RELEASE         : out std_logic_vector(MVB_ITEMS               -1 downto 0);
    -- PCIe tag valid bit
    TAG_VLD             : out std_logic_vector(MVB_ITEMS               -1 downto 0);

    -- DMA DOWN HDR output has delay 2 CLK after TAG output is set

    -- DMA tag corresponding to given PCIe tag
    DMA_DOWN_HDR_TAG    : in  std_logic_vector(MVB_ITEMS*DMA_TAG_WIDTH-1 downto 0);
    -- DMA component ID corresponding to PCIe tag
    DMA_DOWN_HDR_ID     : in  std_logic_vector(MVB_ITEMS*DMA_ID_WIDTH -1 downto 0);

    ---------------------------------------------------------------------------
    -- TX DMA MVB interface
    ---------------------------------------------------------------------------

    -- Upstream headers
    TX_MVB_DATA     : out std_logic_vector(MVB_ITEMS*DMA_DOWNHDR_WIDTH-1 downto 0);
    -- Valid bit for each UP header
    TX_MVB_VLD      : out std_logic_vector(MVB_ITEMS                  -1 downto 0);
    -- Source ready entire UP stream
    TX_MVB_SRC_RDY  : out std_logic
);
end entity PTC_PCIE2DMA_HDR_TRANSFORM;
