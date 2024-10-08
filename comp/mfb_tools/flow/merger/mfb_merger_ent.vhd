-- mfb_merger_ent.vhd: MFB+MVB bus merger
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields

-- ----------------------------------------------------------------------------
--                           Entity declaration
-- ----------------------------------------------------------------------------

-- Merges two input MVB+MFB interfaces in one output interface
-- Contains input FIFOs and output PIPEs.
entity MFB_MERGER is
generic(
    -- =============================
    -- TX MVB characteristics
    -- =============================

    -- number of headers
    MVB_ITEMS           : integer := 2;

    -- =============================
    -- TX MFB characteristics
    -- =============================

    -- number of regions in word
    MFB_REGIONS         : integer := 2;
    -- number of blocks in region
    MFB_REG_SIZE        : integer := 1;
    -- number of items in block
    MFB_BLOCK_SIZE      : integer := 8;
    -- width  of one item (in bits)
    MFB_ITEM_WIDTH      : integer := 32;

    -- width of MFB metadata
    MFB_META_WIDTH      : integer := 0;

    -- =============================
    -- Others
    -- =============================

    -- Width of each MVB item
    -- DMA_DOWNHDR_WIDTH, DMA_UPHDR_WIDTH
    HDR_WIDTH           : integer := DMA_DOWNHDR_WIDTH;

    -- Data/Payload MFB interface required/active on individual input ports
    -- Currently used only in SIMPLE architecture to optimize usage of input/output pipes
    RX0_PAYLOAD_ENABLED : boolean := true;
    RX1_PAYLOAD_ENABLED : boolean := true;

    -- Size of input MVB and MFB FIFOs (in words)
    -- Only used in architecture FULL.
    -- Minimum value is 2!
    INPUT_FIFO_SIZE     : integer := 8;

    -- Width of timeout counter, determines the time when the switch to
    -- the next active MVB/MFB stream occurs.
    SW_TIMEOUT_WIDTH    : natural := 4;

    -- Input PIPEs enable
    -- Only used in architecture SIMPLE.
    -- Input registers is created when this is set to false.
    IN_PIPE_EN          : boolean := false;

    -- Output PIPE enable
    -- Only used in architecture SIMPLE.
    -- Output register is created when this is set to false.
    OUT_PIPE_EN        : boolean := true;

    -- "ULTRASCALE", "7SERIES"
    DEVICE             : string  := "ULTRASCALE"
);
port(
    -- =============================
    -- Common interface
    -- =============================

    CLK              : in  std_logic;
    RESET            : in  std_logic;

    -- =============================
    -- RX interface 0
    -- =============================

    RX0_MVB_HDR      : in  std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
    -- the header is associated with a payload frame on MFB
    RX0_MVB_PAYLOAD  : in  std_logic_vector(MVB_ITEMS          -1 downto 0);
    RX0_MVB_VLD      : in  std_logic_vector(MVB_ITEMS          -1 downto 0);
    RX0_MVB_SRC_RDY  : in  std_logic;
    RX0_MVB_DST_RDY  : out std_logic;

    RX0_MFB_DATA     : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- Allways valid, metadata merged by words
    RX0_MFB_META     : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => '0');
    RX0_MFB_SOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX0_MFB_EOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX0_MFB_SOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    RX0_MFB_EOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    RX0_MFB_SRC_RDY  : in  std_logic;
    RX0_MFB_DST_RDY  : out std_logic;

    -- =============================
    -- RX interface 1
    -- =============================

    RX1_MVB_HDR      : in  std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
    -- the header is associated with a payload frame on MFB
    RX1_MVB_PAYLOAD  : in  std_logic_vector(MVB_ITEMS          -1 downto 0);
    RX1_MVB_VLD      : in  std_logic_vector(MVB_ITEMS          -1 downto 0);
    RX1_MVB_SRC_RDY  : in  std_logic;
    RX1_MVB_DST_RDY  : out std_logic;

    RX1_MFB_DATA     : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- Allways valid, metadata merged by words
    RX1_MFB_META     : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => '0');
    RX1_MFB_SOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX1_MFB_EOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX1_MFB_SOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    RX1_MFB_EOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    RX1_MFB_SRC_RDY  : in  std_logic;
    RX1_MFB_DST_RDY  : out std_logic;

    -- =============================
    -- TX interface
    -- =============================

    TX_MVB_HDR       : out std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
    -- the header is associated with a payload frame on MFB
    TX_MVB_PAYLOAD   : out std_logic_vector(MVB_ITEMS          -1 downto 0);
    TX_MVB_VLD       : out std_logic_vector(MVB_ITEMS          -1 downto 0);
    TX_MVB_SRC_RDY   : out std_logic;
    TX_MVB_DST_RDY   : in  std_logic;

    TX_MFB_DATA      : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- Allways valid, metadata merged by words
    TX_MFB_META      : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    TX_MFB_SOF       : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_EOF       : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_SOF_POS   : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    TX_MFB_EOF_POS   : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    TX_MFB_SRC_RDY   : out std_logic;
    TX_MFB_DST_RDY   : in  std_logic
);
end entity MFB_MERGER;
