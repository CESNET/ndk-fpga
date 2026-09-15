-- mfb_splitter.vhd: MFB+MVB bus splitter
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
--                           Entity Declaration
-- ----------------------------------------------------------------------------

-- Splits RX MFB+MVB interface to two intefaces.
-- Switches packets based on one bit SWITCH for each MVB header.
--
-- .. warning::
--   Headers and frames are paired by order, not by content. The k-th frame on
--   RX MFB belongs to the k-th header that has ``RX_MVB_PAYLOAD(i)='1'``. A
--   header with ``'0'`` takes no frame.
--
entity MFB_SPLITTER is
    generic (
        -- ======================
        -- TX MVB characteristics
        -- ======================

        -- number of headers
        MVB_ITEMS            : integer := 2;
        -- width of each MVB meta item
        MVB_META_WIDTH       : integer := 2;

        -- ======================
        -- TX MFB characteristics
        -- ======================

        -- number of regions in word
        MFB_REGIONS          : integer := 2;
        -- number of blocks in region
        MFB_REG_SIZE         : integer := 1;
        -- number of items in block
        MFB_BLOCK_SIZE       : integer := 8;
        -- width  of one item (in bits)
        MFB_ITEM_WIDTH       : integer := 32;

        -- ===================
        -- Others
        -- ===================

        -- Width of each MVB item
        -- DMA_DOWNHDR_WIDTH, DMA_UPHDR_WIDTH
        HDR_WIDTH            : integer := DMA_DOWNHDR_WIDTH;

        -- Obsolete, use OUT_MVB_FIFO_SIZE instead, which it sets the default of
        MVB_OUTPUT_FIFO_SIZE : integer := 8;

        -- Depth of the output MVB FIFOs in words
        -- Minimum value is 2. They keep the outputs in step with the switch
        -- FIFO inside the splitter and cannot be turned off.
        OUT_MVB_FIFO_SIZE    : integer := MVB_OUTPUT_FIFO_SIZE;

        -- Enable an MFB FIFO on the input of the splitter
        -- true: Holds the frame back until the header that says where to route
        -- it has arrived. A source that puts the header out at the end of the
        -- frame needs it.
        -- false: Direct connection without input buffering
        IN_MFB_FIFO_EN       : boolean := false;

        -- Obsolete, use IN_MFB_FIFO_SIZE instead, which it sets the default of
        MFB_FIFO_DEPTH       : natural := 512;

        -- Depth of the input MFB FIFO in words
        -- Only used when IN_MFB_FIFO_EN is true
        IN_MFB_FIFO_SIZE     : natural := MFB_FIFO_DEPTH;

        -- Enable the output MFB FIFOs. A whole word is routed at once, so
        -- without them the slowest output holds up all the others.
        OUT_MFB_FIFO_EN      : boolean := false;

        -- Depth of the output MFB FIFOs in words
        -- Only used when OUT_MFB_FIFO_EN is true
        OUT_MFB_FIFO_SIZE    : natural := 512;

        -- Obsolete, has no effect. The output registers are inside the splitter
        -- and are not optional.
        USE_OUTREG           : boolean := true;

        -- "ULTRASCALE", "7SERIES"
        DEVICE               : string  := "ULTRASCALE";

        -- "FULL", "SHAKEDOWN"
        FIFOX_MULTI_ARCH     : string  := "SHAKEDOWN"
    );
    port (
        -- ======================
        -- Common interface
        -- ======================

        CLK             : in  std_logic;
        RESET           : in  std_logic;

        -- ======================
        -- RX interface
        -- ======================

        RX_MVB_HDR      : in  std_logic_vector(MVB_ITEMS*HDR_WIDTH     -1 downto 0);
        RX_MVB_META     : in  std_logic_vector(MVB_ITEMS*MVB_META_WIDTH-1 downto 0) := (others => '0');
        -- output select for each header
        RX_MVB_SWITCH   : in  std_logic_vector(MVB_ITEMS               -1 downto 0);
        -- header contains payload in MFB
        RX_MVB_PAYLOAD  : in  std_logic_vector(MVB_ITEMS               -1 downto 0);
        RX_MVB_VLD      : in  std_logic_vector(MVB_ITEMS               -1 downto 0);
        RX_MVB_SRC_RDY  : in  std_logic;
        RX_MVB_DST_RDY  : out std_logic;

        RX_MFB_DATA     : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        RX_MFB_EOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY  : in  std_logic;
        RX_MFB_DST_RDY  : out std_logic;

        -- ======================
        -- TX interface 0
        -- ======================

        TX0_MVB_HDR     : out std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
        TX0_MVB_META    : out std_logic_vector(MVB_ITEMS*MVB_META_WIDTH-1 downto 0);
        TX0_MVB_PAYLOAD : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX0_MVB_VLD     : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX0_MVB_SRC_RDY : out std_logic;
        TX0_MVB_DST_RDY : in  std_logic;

        TX0_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX0_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX0_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX0_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        TX0_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX0_MFB_SRC_RDY : out std_logic;
        TX0_MFB_DST_RDY : in  std_logic;

        -- ======================
        -- TX interface 1
        -- ======================

        TX1_MVB_HDR     : out std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
        TX1_MVB_META    : out std_logic_vector(MVB_ITEMS*MVB_META_WIDTH-1 downto 0);
        TX1_MVB_PAYLOAD : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX1_MVB_VLD     : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX1_MVB_SRC_RDY : out std_logic;
        TX1_MVB_DST_RDY : in  std_logic;

        TX1_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX1_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX1_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX1_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        TX1_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX1_MFB_SRC_RDY : out std_logic;
        TX1_MFB_DST_RDY : in  std_logic

    );
end entity;

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture FULL of MFB_SPLITTER is

    -- MFB_SPLITTER_GEN carries one opaque item per header, so the metadata
    -- rides with its header.
    constant ITEM_WIDTH : natural := HDR_WIDTH + MVB_META_WIDTH;

    signal rx_mvb_item     : std_logic_vector(MVB_ITEMS*ITEM_WIDTH-1 downto 0);

    signal tx_mvb_item     : slv_array_t(2-1 downto 0)(MVB_ITEMS*ITEM_WIDTH-1 downto 0);
    signal tx_mvb_payload  : slv_array_t(2-1 downto 0)(MVB_ITEMS-1 downto 0);
    signal tx_mvb_vld      : slv_array_t(2-1 downto 0)(MVB_ITEMS-1 downto 0);
    signal tx_mvb_src_rdy  : std_logic_vector(2-1 downto 0);
    signal tx_mvb_dst_rdy  : std_logic_vector(2-1 downto 0);

    signal tx_mfb_data     : slv_array_t(2-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal tx_mfb_sof      : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal tx_mfb_eof      : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal tx_mfb_sof_pos  : slv_array_t(2-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal tx_mfb_eof_pos  : slv_array_t(2-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal tx_mfb_src_rdy  : std_logic_vector(2-1 downto 0);
    signal tx_mfb_dst_rdy  : std_logic_vector(2-1 downto 0);

begin

    rx_mvb_item_g : for i in 0 to MVB_ITEMS-1 generate
        rx_mvb_item((i+1)*ITEM_WIDTH-1 downto i*ITEM_WIDTH) <= RX_MVB_META((i+1)*MVB_META_WIDTH-1 downto i*MVB_META_WIDTH) & RX_MVB_HDR((i+1)*HDR_WIDTH-1 downto i*HDR_WIDTH);
    end generate;

    splitter_i : entity work.MFB_SPLITTER_GEN
    generic map (
        SPLITTER_OUTPUTS  => 2,
        MVB_ITEMS         => MVB_ITEMS,
        MVB_ITEM_WIDTH    => ITEM_WIDTH,
        MFB_REGIONS       => MFB_REGIONS,
        MFB_REG_SIZE      => MFB_REG_SIZE,
        MFB_BLOCK_SIZE    => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH    => MFB_ITEM_WIDTH,
        IN_MFB_FIFO_EN    => IN_MFB_FIFO_EN,
        IN_MFB_FIFO_SIZE  => IN_MFB_FIFO_SIZE,
        OUT_MVB_FIFO_SIZE => OUT_MVB_FIFO_SIZE,
        OUT_MFB_FIFO_EN   => OUT_MFB_FIFO_EN,
        OUT_MFB_FIFO_SIZE => OUT_MFB_FIFO_SIZE,
        FIFOX_MULTI_ARCH  => FIFOX_MULTI_ARCH,
        DEVICE            => DEVICE
    )
    port map (
        CLK   => CLK,
        RESET => RESET,

        RX_MVB_DATA    => rx_mvb_item,
        RX_MVB_SWITCH  => RX_MVB_SWITCH,
        RX_MVB_PAYLOAD => RX_MVB_PAYLOAD,
        RX_MVB_VLD     => RX_MVB_VLD,
        RX_MVB_SRC_RDY => RX_MVB_SRC_RDY,
        RX_MVB_DST_RDY => RX_MVB_DST_RDY,

        RX_MFB_DATA    => RX_MFB_DATA,
        RX_MFB_SOF     => RX_MFB_SOF,
        RX_MFB_EOF     => RX_MFB_EOF,
        RX_MFB_SOF_POS => RX_MFB_SOF_POS,
        RX_MFB_EOF_POS => RX_MFB_EOF_POS,
        RX_MFB_SRC_RDY => RX_MFB_SRC_RDY,
        RX_MFB_DST_RDY => RX_MFB_DST_RDY,

        TX_MVB_DATA    => tx_mvb_item,
        TX_MVB_PAYLOAD => tx_mvb_payload,
        TX_MVB_VLD     => tx_mvb_vld,
        TX_MVB_SRC_RDY => tx_mvb_src_rdy,
        TX_MVB_DST_RDY => tx_mvb_dst_rdy,

        TX_MFB_DATA    => tx_mfb_data,
        TX_MFB_SOF     => tx_mfb_sof,
        TX_MFB_EOF     => tx_mfb_eof,
        TX_MFB_SOF_POS => tx_mfb_sof_pos,
        TX_MFB_EOF_POS => tx_mfb_eof_pos,
        TX_MFB_SRC_RDY => tx_mfb_src_rdy,
        TX_MFB_DST_RDY => tx_mfb_dst_rdy
    );

    tx_mvb_item_g : for i in 0 to MVB_ITEMS-1 generate
        TX0_MVB_HDR((i+1)*HDR_WIDTH-1 downto i*HDR_WIDTH) <= tx_mvb_item(0)(i*ITEM_WIDTH+HDR_WIDTH-1 downto i*ITEM_WIDTH);
        TX1_MVB_HDR((i+1)*HDR_WIDTH-1 downto i*HDR_WIDTH) <= tx_mvb_item(1)(i*ITEM_WIDTH+HDR_WIDTH-1 downto i*ITEM_WIDTH);

        TX0_MVB_META((i+1)*MVB_META_WIDTH-1 downto i*MVB_META_WIDTH) <= tx_mvb_item(0)((i+1)*ITEM_WIDTH-1 downto i*ITEM_WIDTH+HDR_WIDTH);
        TX1_MVB_META((i+1)*MVB_META_WIDTH-1 downto i*MVB_META_WIDTH) <= tx_mvb_item(1)((i+1)*ITEM_WIDTH-1 downto i*ITEM_WIDTH+HDR_WIDTH);
    end generate;

    TX0_MVB_PAYLOAD   <= tx_mvb_payload(0);
    TX0_MVB_VLD       <= tx_mvb_vld(0);
    TX0_MVB_SRC_RDY   <= tx_mvb_src_rdy(0);
    tx_mvb_dst_rdy(0) <= TX0_MVB_DST_RDY;

    TX1_MVB_PAYLOAD   <= tx_mvb_payload(1);
    TX1_MVB_VLD       <= tx_mvb_vld(1);
    TX1_MVB_SRC_RDY   <= tx_mvb_src_rdy(1);
    tx_mvb_dst_rdy(1) <= TX1_MVB_DST_RDY;

    TX0_MFB_DATA      <= tx_mfb_data(0);
    TX0_MFB_SOF       <= tx_mfb_sof(0);
    TX0_MFB_EOF       <= tx_mfb_eof(0);
    TX0_MFB_SOF_POS   <= tx_mfb_sof_pos(0);
    TX0_MFB_EOF_POS   <= tx_mfb_eof_pos(0);
    TX0_MFB_SRC_RDY   <= tx_mfb_src_rdy(0);
    tx_mfb_dst_rdy(0) <= TX0_MFB_DST_RDY;

    TX1_MFB_DATA      <= tx_mfb_data(1);
    TX1_MFB_SOF       <= tx_mfb_sof(1);
    TX1_MFB_EOF       <= tx_mfb_eof(1);
    TX1_MFB_SOF_POS   <= tx_mfb_sof_pos(1);
    TX1_MFB_EOF_POS   <= tx_mfb_eof_pos(1);
    TX1_MFB_SRC_RDY   <= tx_mfb_src_rdy(1);
    tx_mfb_dst_rdy(1) <= TX1_MFB_DST_RDY;

end architecture;
