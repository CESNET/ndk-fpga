-- mfb_merger.vhd: MFB+MVB bus merger with two inputs
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

-- Merges two MVB+MFB inputs into one output.
--
-- .. warning::
--   Headers and frames are paired by order, not by content. On one input the
--   k-th frame on MFB belongs to the k-th header that has
--   ``RXx_MVB_PAYLOAD(i)='1'``. A header with ``'0'`` takes no frame.
--
entity MFB_MERGER is
    generic (
        -- =====================================================================
        -- MVB INTERFACE PARAMETERS
        -- =====================================================================

        -- Number of MVB headers per word
        MVB_ITEMS           : integer := 2;
        -- Width of one MVB header in bits
        HDR_WIDTH           : integer := DMA_DOWNHDR_WIDTH;

        -- =====================================================================
        -- MFB INTERFACE PARAMETERS
        -- =====================================================================

        -- Number of Regions per MFB word
        MFB_REGIONS         : integer := 2;
        -- Number of Blocks per Region
        MFB_REG_SIZE        : integer := 1;
        -- Number of Items per Block
        MFB_BLOCK_SIZE      : integer := 8;
        -- Width of one MFB Item in bits
        MFB_ITEM_WIDTH      : integer := 32;
        -- Width of MFB metadata in bits, 0 disables it
        MFB_META_WIDTH      : integer := 0;

        -- =====================================================================
        -- GENERAL PARAMETERS
        -- =====================================================================

        -- MFB data payload enable for the RX0 input port
        -- false: MVB headers only, the MFB path is optimized away
        RX0_PAYLOAD_ENABLED : boolean := true;
        -- MFB data payload enable for the RX1 input port
        RX1_PAYLOAD_ENABLED : boolean := true;

        -- Enable the input MFB FIFOs
        IN_MFB_FIFO_EN      : boolean := false;
        -- Obsolete, use IN_MFB_FIFO_SIZE instead, which it sets the default of
        INPUT_FIFO_SIZE     : integer := 8;
        -- Depth of the input MFB FIFOs in words, minimum value is 2
        IN_MFB_FIFO_SIZE    : integer := INPUT_FIFO_SIZE;
        -- Enable the input MVB FIFOs
        IN_MVB_FIFO_EN      : boolean := false;
        -- Depth of the input MVB FIFOs in words, minimum value is 2
        IN_MVB_FIFO_SIZE    : integer := 8;

        -- Width of the stream switch timeout counter
        SW_TIMEOUT_WIDTH    : natural := 4;
        -- Depth of the switch FIFO in items
        SW_FIFO_ITEMS       : natural := MVB_ITEMS*32;

        -- Enable the input PIPE stages
        IN_PIPE_EN          : boolean := false;
        -- Enable the output PIPE stage
        OUT_PIPE_EN         : boolean := true;

        -- Architecture of the internal FIFOX_MULTI, "SHAKEDOWN" or "FULL"
        FIFOX_MULTI_ARCH    : string := "SHAKEDOWN";

        -- Target device family
        DEVICE              : string  := "ULTRASCALE"
    );
    port (
        -- =====================================================================
        -- COMMON SIGNALS
        -- =====================================================================

        CLK                 : in  std_logic;
        RESET               : in  std_logic;

        -- =====================================================================
        -- RX INTERFACE 0
        -- =====================================================================

        RX0_MVB_HDR         : in  std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
        -- Bit i announces that header i has a frame on MFB
        RX0_MVB_PAYLOAD     : in  std_logic_vector(MVB_ITEMS          -1 downto 0);
        RX0_MVB_VLD         : in  std_logic_vector(MVB_ITEMS          -1 downto 0);
        RX0_MVB_SRC_RDY     : in  std_logic;
        RX0_MVB_DST_RDY     : out std_logic;

        RX0_MFB_DATA        : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- Passed to the output unchanged
        RX0_MFB_META        : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => '0');
        RX0_MFB_SOF         : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX0_MFB_EOF         : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX0_MFB_SOF_POS     : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        RX0_MFB_EOF_POS     : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX0_MFB_SRC_RDY     : in  std_logic;
        RX0_MFB_DST_RDY     : out std_logic;

        -- =====================================================================
        -- RX INTERFACE 1
        -- =====================================================================

        RX1_MVB_HDR         : in  std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
        RX1_MVB_PAYLOAD     : in  std_logic_vector(MVB_ITEMS          -1 downto 0);
        RX1_MVB_VLD         : in  std_logic_vector(MVB_ITEMS          -1 downto 0);
        RX1_MVB_SRC_RDY     : in  std_logic;
        RX1_MVB_DST_RDY     : out std_logic;

        RX1_MFB_DATA        : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX1_MFB_META        : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => '0');
        RX1_MFB_SOF         : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX1_MFB_EOF         : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX1_MFB_SOF_POS     : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        RX1_MFB_EOF_POS     : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX1_MFB_SRC_RDY     : in  std_logic;
        RX1_MFB_DST_RDY     : out std_logic;

        -- =====================================================================
        -- TX INTERFACE
        -- =====================================================================

        TX_MVB_HDR          : out std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
        TX_MVB_PAYLOAD      : out std_logic_vector(MVB_ITEMS          -1 downto 0);
        TX_MVB_VLD          : out std_logic_vector(MVB_ITEMS          -1 downto 0);
        TX_MVB_SRC_RDY      : out std_logic;
        TX_MVB_DST_RDY      : in  std_logic;

        TX_MFB_DATA         : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_META         : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        TX_MFB_SOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF          : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        TX_MFB_EOF_POS      : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY      : out std_logic;
        TX_MFB_DST_RDY      : in  std_logic
    );
end entity;

architecture FULL of MFB_MERGER is

    constant PAYLOAD_EN : b_array_t(2-1 downto 0) := (0 => RX0_PAYLOAD_ENABLED, 1 => RX1_PAYLOAD_ENABLED);

    signal rx_mvb_hdr     : slv_array_t(2-1 downto 0)(MVB_ITEMS*HDR_WIDTH-1 downto 0);
    signal rx_mvb_payload : slv_array_t(2-1 downto 0)(MVB_ITEMS-1 downto 0);
    signal rx_mvb_vld     : slv_array_t(2-1 downto 0)(MVB_ITEMS-1 downto 0);
    signal rx_mvb_src_rdy : std_logic_vector(2-1 downto 0);
    signal rx_mvb_dst_rdy : std_logic_vector(2-1 downto 0);

    signal rx_mfb_data    : slv_array_t(2-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal rx_mfb_meta    : slv_array_t(2-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal rx_mfb_sof     : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_mfb_eof     : slv_array_t(2-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_mfb_sof_pos : slv_array_t(2-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal rx_mfb_eof_pos : slv_array_t(2-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal rx_mfb_src_rdy : std_logic_vector(2-1 downto 0);
    signal rx_mfb_dst_rdy : std_logic_vector(2-1 downto 0);

begin

    rx_mvb_hdr     <= (0 => RX0_MVB_HDR,     1 => RX1_MVB_HDR);
    rx_mvb_payload <= (0 => RX0_MVB_PAYLOAD, 1 => RX1_MVB_PAYLOAD);
    rx_mvb_vld     <= (0 => RX0_MVB_VLD,     1 => RX1_MVB_VLD);
    rx_mvb_src_rdy <= (0 => RX0_MVB_SRC_RDY, 1 => RX1_MVB_SRC_RDY);

    RX0_MVB_DST_RDY <= rx_mvb_dst_rdy(0);
    RX1_MVB_DST_RDY <= rx_mvb_dst_rdy(1);

    rx_mfb_data    <= (0 => RX0_MFB_DATA,    1 => RX1_MFB_DATA);
    rx_mfb_meta    <= (0 => RX0_MFB_META,    1 => RX1_MFB_META);
    rx_mfb_sof     <= (0 => RX0_MFB_SOF,     1 => RX1_MFB_SOF);
    rx_mfb_eof     <= (0 => RX0_MFB_EOF,     1 => RX1_MFB_EOF);
    rx_mfb_sof_pos <= (0 => RX0_MFB_SOF_POS, 1 => RX1_MFB_SOF_POS);
    rx_mfb_eof_pos <= (0 => RX0_MFB_EOF_POS, 1 => RX1_MFB_EOF_POS);
    rx_mfb_src_rdy <= (0 => RX0_MFB_SRC_RDY, 1 => RX1_MFB_SRC_RDY);

    RX0_MFB_DST_RDY <= rx_mfb_dst_rdy(0);
    RX1_MFB_DST_RDY <= rx_mfb_dst_rdy(1);

    merger_i : entity work.MFB_MERGER_GEN
    generic map (
        MERGER_INPUTS       => 2,
        MVB_ITEMS           => MVB_ITEMS,
        MVB_ITEM_WIDTH      => HDR_WIDTH,
        MFB_REGIONS         => MFB_REGIONS,
        MFB_REG_SIZE        => MFB_REG_SIZE,
        MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH,
        MFB_META_WIDTH      => MFB_META_WIDTH,
        IN_MFB_FIFO_EN      => IN_MFB_FIFO_EN,
        IN_MFB_FIFO_SIZE    => IN_MFB_FIFO_SIZE,
        IN_MVB_FIFO_EN      => IN_MVB_FIFO_EN,
        IN_MVB_FIFO_SIZE    => IN_MVB_FIFO_SIZE,
        SW_FIFO_ITEMS       => SW_FIFO_ITEMS,
        RX_PAYLOAD_EN       => PAYLOAD_EN,
        SW_TIMEOUT_WIDTH    => SW_TIMEOUT_WIDTH,
        IN_PIPE_EN          => IN_PIPE_EN,
        OUT_PIPE_EN         => OUT_PIPE_EN,
        FIFOX_MULTI_ARCH    => FIFOX_MULTI_ARCH,
        DEVICE              => DEVICE
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,

        RX_MVB_DATA    => rx_mvb_hdr,
        RX_MVB_PAYLOAD => rx_mvb_payload,
        RX_MVB_VLD     => rx_mvb_vld,
        RX_MVB_SRC_RDY => rx_mvb_src_rdy,
        RX_MVB_DST_RDY => rx_mvb_dst_rdy,

        RX_MFB_DATA    => rx_mfb_data,
        RX_MFB_META    => rx_mfb_meta,
        RX_MFB_SOF     => rx_mfb_sof,
        RX_MFB_EOF     => rx_mfb_eof,
        RX_MFB_SOF_POS => rx_mfb_sof_pos,
        RX_MFB_EOF_POS => rx_mfb_eof_pos,
        RX_MFB_SRC_RDY => rx_mfb_src_rdy,
        RX_MFB_DST_RDY => rx_mfb_dst_rdy,

        TX_MVB_DATA    => TX_MVB_HDR,
        TX_MVB_PAYLOAD => TX_MVB_PAYLOAD,
        TX_MVB_VLD     => TX_MVB_VLD,
        TX_MVB_SRC_RDY => TX_MVB_SRC_RDY,
        TX_MVB_DST_RDY => TX_MVB_DST_RDY,

        TX_MFB_DATA    => TX_MFB_DATA,
        TX_MFB_META    => TX_MFB_META,
        TX_MFB_SOF     => TX_MFB_SOF,
        TX_MFB_EOF     => TX_MFB_EOF,
        TX_MFB_SOF_POS => TX_MFB_SOF_POS,
        TX_MFB_EOF_POS => TX_MFB_EOF_POS,
        TX_MFB_SRC_RDY => TX_MFB_SRC_RDY,
        TX_MFB_DST_RDY => TX_MFB_DST_RDY
    );

end architecture;
