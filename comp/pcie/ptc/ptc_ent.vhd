-- ptc_ent.vhd: PCIE_TRANSACTION_CTRL entity
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
--                           Description
-- ----------------------------------------------------------------------------
-- This unit serves for connection to PCIe Endpoint Requester interface using MVB+MFB bus interface.

-- ----------------------------------------------------------------------------
--                             Entity
-- ----------------------------------------------------------------------------

entity PCIE_TRANSACTION_CTRL is
generic(
    -- Number of DMA ports per one PTC, possible values: 1, 2.
    DMA_PORTS           : integer := 1;

    -- ==================
    -- MVB UP definition
    -- ==================

    -- Number of items (headers) in PTC word
    MVB_UP_ITEMS        : integer := 2;
    -- Number of items (headers) in DMA word, allowed values: MVB_UP_ITEMS, 2*MVB_UP_ITEMS
    DMA_MVB_UP_ITEMS    : integer := MVB_UP_ITEMS;

    -- ==================
    -- MFB UP definition
    -- ==================

    -- Number of regions in word
    MFB_UP_REGIONS      : integer := 2;
    -- Number of blocks in region
    MFB_UP_REG_SIZE     : integer := 1;
    -- Number of items in block
    MFB_UP_BLOCK_SIZE   : integer := 8;
    -- Width of one item (in bits)
    MFB_UP_ITEM_WIDTH   : integer := 32;
    -- Number of regions in DMA UP word (DMA MFB word is converted from 512b to 256b in UP MFB asfifo)
    -- for Ultrascale equals MFB_UP_REGIONS
    -- for Virtex7 equals 2*MFB_UP_REGIONS
    DMA_MFB_UP_REGIONS  : integer := MFB_UP_REGIONS;

    -- ===================
    -- MVB DOWN definition
    -- ===================

    -- Number of items (headers) in PTC word
    MVB_DOWN_ITEMS      : integer := 4;
    -- Number of items (headers) in DMA word, allowed values: MVB_DOWN_ITEMS, 2*MVB_DOWN_ITEMS
    DMA_MVB_DOWN_ITEMS  : integer := MVB_DOWN_ITEMS;

    -- ====================
    -- MFB DOWN definition
    -- ====================

    -- Number of regions in word
    MFB_DOWN_REGIONS    : integer := 4;
    -- Number of blocks in region
    MFB_DOWN_REG_SIZE   : integer := 1;
    -- Number of items in block
    MFB_DOWN_BLOCK_SIZE : integer := 4;
    -- Width of one item (in bits)
    MFB_DOWN_ITEM_WIDTH : integer := 32;
    -- Number of regions in DMA UP word (DMA MFB word is converted from 256b to 512b in DOWN MFB asfifo)
    -- for Ultrascale equals MFB_DOWN_REGIONS
    -- for Virtex7 equals 2*MFB_DOWN_REGIONS
    DMA_MFB_DOWN_REGIONS : integer := MFB_DOWN_REGIONS;

    -- Width of MVB headers is defined in dma_bus_pack
    -- Width of MFB data is MFB_REGIONS * MFB_REG_SIZE * MFB_BLOCK_SIZE * MFB_ITEM_WIDTH

    -- Width of one PCIe UP header (defined in PCIe specification) (must be devisible by MFB_DOWN_ITEM_WIDTH)
    PCIE_UPHDR_WIDTH   : integer := 128;

    -- Width of one PCIe DOWN header (defined in PCIe specification) (minimum is 3*4*8) (must be devisible by MFB_DOWN_ITEM_WIDTH)
    PCIE_DOWNHDR_WIDTH : integer := 3*4*8;

    -- PCIe trabsaction prefix width (prefixes not supported yet)
    PCIE_PREFIX_WIDTH  : integer := 32;

    -- Width of DMA Tag field in MVB header (maximum defined by range in dma_bus_pack)
    DMA_TAG_WIDTH     : integer := DMA_REQUEST_TAG'high - DMA_REQUEST_TAG'low + 1;
    -- Width of DMA Unit ID field in MVB header (maximum defined by range in dma_bus_pack)
    DMA_ID_WIDTH      : integer := DMA_REQUEST_UNITID'high - DMA_REQUEST_UNITID'low + 1;

    -- Width of Tag field in PCIe header (maximum 8 defined in PCIe specification)
    PCIE_TAG_WIDTH    : integer := 8;

    -- Maximum write request (payload) size (in DWORDs)
    -- Only needed for setting MFB FIFO sizes
    MPS               : natural := 512/4;
    -- Maximum read write request size (in DWORDs)
    -- Only needed when DMA_PORTS>1 for setting MFB FIFO sizes
    MRRS              : natural := 512/4;

    -- UPSTREAM input ASFIFO size
    UP_ASFIFO_ITEMS   : integer := 512;
    -- DOWNSTREAM output ASFIFO size
    -- minimum for wide BRAM FIFO
    DOWN_ASFIFO_ITEMS : integer := 512;

    -- DOWNSTREAM completion storage FIFO size
    DOWN_FIFO_ITEMS   : integer := 512;

    -- Width of UP AXI signal RQ_TUSER (defined in PCIe specification)
    -- UltraScale+ -> 137; Virtex7 -> 60;
    RQ_TUSER_WIDTH    : integer := 137;

    -- Width of DOWN AXI signal RC_TUSER (defined in PCIe specification)
    -- UltraScale+ -> 161; Virtex7 -> 75;
    RC_TUSER_WIDTH    : integer := 161;

    -- CPL credits checking:
    -- Each credit represents one available 64B or 128B word in receiving buffer.
    -- The goal is to calculate, whether UP read request's response fits in available words in receiving buffer.

    -- Auto-assign PCIe tags
    -- true  -> Tag Manager automaticaly generates remapped tags and sends transactions up with these tags.
    -- false -> Tag Manager receives tags from PCIe endpoint via the TAG_ASSIGN interface.
    --          (Can only be used on Xilinx FPGAs)
    -- This option must correspond with the PCIe settings.
    AUTO_ASSIGN_TAGS    : boolean := true;

    -- Target device
    -- "VIRTEX6", "7SERIES", "ULTRASCALE", "STRATIX10"
    DEVICE              : string  := "ULTRASCALE";
    -- Connected PCIe endpoint type ("H_TILE" or "P_TILE" or "R_TILE") (only relevant on Intel FPGAs)
    ENDPOINT_TYPE       : string  := "H_TILE"
);
port(
    -- ========================================================================
    -- Common interface
    -- ========================================================================

    CLK            : in  std_logic;
    RESET          : in  std_logic;

    -- UP input and DOWN output interface CLK
    CLK_DMA        : in  std_logic;
    RESET_DMA      : in  std_logic;

    -- ========================================================================
    -- UPSTREAM interfaces
    --
    -- Input from DMA Module (MVB+MFB bus) (runs on CLK_DMA)
    -- ========================================================================

    -- MVB items
    UP_MVB_DATA    : in  slv_array_t(DMA_PORTS-1 downto 0)(DMA_MVB_UP_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
    -- MVB item valid
    UP_MVB_VLD     : in  slv_array_t(DMA_PORTS-1 downto 0)(DMA_MVB_UP_ITEMS                -1 downto 0);
    UP_MVB_SRC_RDY : in  std_logic_vector(DMA_PORTS-1 downto 0);
    UP_MVB_DST_RDY : out std_logic_vector(DMA_PORTS-1 downto 0);

    -- MFB data word
    UP_MFB_DATA    : in  slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH-1 downto 0);
    -- MFB region contains start of frame
    UP_MFB_SOF     : in  slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS-1 downto 0);
    -- MFB region contains end of frame
    UP_MFB_EOF     : in  slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS-1 downto 0);
    -- address of block of region's SOF
    UP_MFB_SOF_POS : in  slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE))-1 downto 0);
    -- address of item of region's EOF
    UP_MFB_EOF_POS : in  slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE))-1 downto 0);
    UP_MFB_SRC_RDY : in  std_logic_vector(DMA_PORTS-1 downto 0);
    UP_MFB_DST_RDY : out std_logic_vector(DMA_PORTS-1 downto 0);

    -- ========================================================================
    -- Header output to PCIe Endpoint (Requester request interface (RQ))
    --
    -- Used in Intel DEVICEs with P_TILE Endpoint type
    -- ========================================================================

    RQ_MVB_HDR_DATA    : out std_logic_vector(MFB_UP_REGIONS*PCIE_UPHDR_WIDTH-1 downto 0);
    -- valid together with HDR_DATA
    RQ_MVB_PREFIX_DATA : out std_logic_vector(MFB_UP_REGIONS*PCIE_PREFIX_WIDTH-1 downto 0);
    RQ_MVB_VLD         : out std_logic_vector(MFB_UP_REGIONS-1 downto 0);
 --RQ_MVB_SRC_RDY     : out std_logic; -- only RQ_MFB_SRC_RDY is used
 --RQ_MVB_DST_RDY     : in  std_logic; -- only RQ_MFB_DST_RDY is used

    -- ========================================================================
    -- Output to PCIe Endpoint (Requester request interface (RQ))
    --
    -- Used in Intel DEVICEs
    -- ========================================================================

    RQ_MFB_DATA    : out std_logic_vector(MFB_UP_REGIONS*MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE*MFB_UP_ITEM_WIDTH-1 downto 0);
    RQ_MFB_SOF     : out std_logic_vector(MFB_UP_REGIONS-1 downto 0);
    RQ_MFB_EOF     : out std_logic_vector(MFB_UP_REGIONS-1 downto 0);
    RQ_MFB_SOF_POS : out std_logic_vector(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE))-1 downto 0);
    RQ_MFB_EOF_POS : out std_logic_vector(MFB_UP_REGIONS*max(1,log2(MFB_UP_REG_SIZE*MFB_UP_BLOCK_SIZE))-1 downto 0);
    RQ_MFB_SRC_RDY : out std_logic;
    RQ_MFB_BE      : out std_logic_vector(MFB_UP_REGIONS*8-1 downto 0);
    RQ_MFB_DST_RDY : in  std_logic := '0';

    -- ========================================================================
    -- DOWNSTREAM interfaces
    --
    -- Header input from PCIe Endpoint (Requester Completion interface (RC))
    -- Used in Intel DEVICEs with P_TILE Endpoint type
    -- ========================================================================

    RC_MVB_HDR_DATA    : in  std_logic_vector(MFB_DOWN_REGIONS*PCIE_DOWNHDR_WIDTH-1 downto 0) := (others => '0');
    -- valid together with HDR_DATA
    RC_MVB_PREFIX_DATA : in  std_logic_vector(MFB_DOWN_REGIONS*PCIE_PREFIX_WIDTH-1 downto 0)  := (others => '0');
    RC_MVB_VLD         : in  std_logic_vector(MFB_DOWN_REGIONS-1 downto 0) := (others => '0');
 --RC_MVB_SRC_RDY     : in  std_logic; -- only RC_MFB_SRC_RDY is used
 --RC_MVB_DST_RDY     : out std_logic; -- only RC_MFB_DST_RDY is used

    -- ========================================================================
    -- Input from PCIe Endpoint (Requester Completion Interface (RC))
    -- Used in Intel DEVICEs
    -- ========================================================================

    RC_MFB_DATA    : in  std_logic_vector(MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0) := (others => '0');
    RC_MFB_SOF     : in  std_logic_vector(MFB_DOWN_REGIONS-1 downto 0)                                                           := (others => '0');
    RC_MFB_EOF     : in  std_logic_vector(MFB_DOWN_REGIONS-1 downto 0)                                                           := (others => '0');
    RC_MFB_SOF_POS : in  std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0)                            := (others => '0');
    RC_MFB_EOF_POS : in  std_logic_vector(MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0)        := (others => '0');
    RC_MFB_SRC_RDY : in  std_logic                                                                                               := '0';
    RC_MFB_DST_RDY : out std_logic;

    -- ========================================================================
    -- Output to DMA Module (MVB+MFB bus) (runs on CLK_DMA)
    -- ========================================================================

    -- MVB items
    DOWN_MVB_DATA    : out slv_array_t(DMA_PORTS-1 downto 0)(DMA_MVB_DOWN_ITEMS*DMA_DOWNHDR_WIDTH-1 downto 0);
    -- MVB item valid
    DOWN_MVB_VLD     : out slv_array_t(DMA_PORTS-1 downto 0)(DMA_MVB_DOWN_ITEMS                  -1 downto 0);
    DOWN_MVB_SRC_RDY : out std_logic_vector(DMA_PORTS-1 downto 0);
    DOWN_MVB_DST_RDY : in  std_logic_vector(DMA_PORTS-1 downto 0);

    -- MFB data word
    DOWN_MFB_DATA    : out slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE*MFB_DOWN_ITEM_WIDTH-1 downto 0);
    -- MFB region contains start of frame
    DOWN_MFB_SOF     : out slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS-1 downto 0);
    -- MFB region contains end of frame
    DOWN_MFB_EOF     : out slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS-1 downto 0);
    -- address of block of region's SOF
    DOWN_MFB_SOF_POS : out slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE))-1 downto 0);
    -- address of item of region's EOF
    DOWN_MFB_EOF_POS : out slv_array_t(DMA_PORTS-1 downto 0)(DMA_MFB_DOWN_REGIONS*max(1,log2(MFB_DOWN_REG_SIZE*MFB_DOWN_BLOCK_SIZE))-1 downto 0);
    DOWN_MFB_SRC_RDY : out std_logic_vector(DMA_PORTS-1 downto 0);
    DOWN_MFB_DST_RDY : in  std_logic_vector(DMA_PORTS-1 downto 0);

    -- ========================================================================
    -- Tag assigning interface to PCIe endpoint
    -- ========================================================================

    -- Configuration Status Interface
    -- Read completion boundary status ('0' = RCB is 64B, '1' = RCB is 128B)
    RCB_SIZE       : in  std_logic;

    -- PCIe tag assigned to send transaction
    TAG_ASSIGN     : in  std_logic_vector(MVB_UP_ITEMS*PCIE_TAG_WIDTH-1 downto 0);
    -- Valid bit for assigned tags
    TAG_ASSIGN_VLD : in  std_logic_vector(MVB_UP_ITEMS               -1 downto 0)
);
end entity PCIE_TRANSACTION_CTRL;
