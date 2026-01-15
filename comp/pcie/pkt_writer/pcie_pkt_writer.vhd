-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all;


-- =========================================================================
--  Basic description (more information in README)
-- =========================================================================
--
-- This module accepts packets and the address to which it shall be written into memory.
-- It splits packets according to the PCIe MTU and memory page boundaries.
-- Then it generates an Upstream DMA header for each of these packet parts.
-- Its output interface is compatible with the PTC module.
--
-- Input packets are expected to start at the beginning of the word (Item 0).
--
-- Check out this :ref:`diagram <ppw_toplevel_diagram>` for a top-level view of the PCIe Packet Writer's architecture.
--
entity PCIE_PKT_WRITER is
    generic (
        -- ========================================================
        -- MFB parameters
        -- ========================================================

        -- Number of MFB Regions in a word, cannot handle more than 1.
        MFB_REGIONS     : natural := 1;
        MFB_REGION_SIZE : natural := 8;
        MFB_BLOCK_SIZE  : natural := 8;
        MFB_ITEM_WIDTH  : natural := 8;

        -- ========================================================
        -- Other parameters
        -- ========================================================

        -- Maximum packet size (in bytes).
        PKT_MTU        : integer := 2**12;
        PCIE_MPS_WIDTH : integer := 15;
        ADDRESS_WIDTH  : natural := 64;
        -- Size of a RAM page (in bytes).
        -- Must be a power of two.
        PAGE_SIZE      : natural := 4096;
        DEVICE         : string := "AGILEX"
    );
    port (
        CLK            : in std_logic;
        RESET          : in std_logic;

        -- Specifies the currently configured max PCIe write request (in bytes).
        -- PCIe specification allows at least 128.
        PCIE_MPS       : in  std_logic_vector(PCIE_MPS_WIDTH-1 downto 0);

        -- ========================================================
        -- RX Interface
        -- ========================================================

        RX_MVB_ADDRESS : in  std_logic_vector(MFB_REGIONS*ADDRESS_WIDTH-1 downto 0);
        RX_MVB_LENGTH  : in  std_logic_vector(MFB_REGIONS*log2(PKT_MTU+1)-1 downto 0);
        RX_MVB_VLD     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MVB_SRC_RDY : in  std_logic;
        RX_MVB_DST_RDY : out std_logic;

        RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;

        -- ========================================================
        -- TX Interface
        -- ========================================================

        -- Contains DMA Upstream header
        TX_MVB_DATA    : out std_logic_vector(MFB_REGIONS*DMA_UPHDR_WIDTH-1 downto 0);
        TX_MVB_VLD     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MVB_SRC_RDY : out std_logic;
        TX_MVB_DST_RDY : in  std_logic;

        TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of PCIE_PKT_WRITER is

    -- =====================================================================
    --                                CONSTANTS
    -- =====================================================================

    constant REGION_WIDTH  : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant WORD_WIDTH    : natural := MFB_REGIONS*REGION_WIDTH;
    constant SOF_POS_WIDTH : natural := max(1, log2(MFB_REGION_SIZE));
    constant EOF_POS_WIDTH : natural := max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));

    -- =====================================================================
    --                                 SIGNALS
    -- =====================================================================

    signal instr_address         : std_logic_vector(MFB_REGIONS*ADDRESS_WIDTH-1 downto 0);
    signal instr_length          : std_logic_vector(MFB_REGIONS*log2(PKT_MTU+1)-1 downto 0);
    signal instr_last            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal instr_valid           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal instr_src_rdy         : std_logic;
    signal instr_dst_rdy         : std_logic;

    signal fifo_tx_mfb_data      : std_logic_vector(WORD_WIDTH-1 downto 0);
    signal fifo_tx_mfb_sof_pos   : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal fifo_tx_mfb_eof_pos   : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal fifo_tx_mfb_sof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fifo_tx_mfb_eof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fifo_tx_mfb_src_rdy   : std_logic;
    signal fifo_tx_mfb_dst_rdy   : std_logic;

    signal hdrgen_rx_mvb_address : std_logic_vector(MFB_REGIONS*ADDRESS_WIDTH-1 downto 0);
    signal hdrgen_rx_mvb_length  : std_logic_vector(MFB_REGIONS*log2(PKT_MTU+1)-1 downto 0);
    signal hdrgen_rx_mvb_valid   : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal hdrgen_rx_mvb_src_rdy : std_logic;
    signal hdrgen_rx_mvb_dst_rdy : std_logic;

begin

    assert MFB_REGIONS = 1
        report "PCIE_PKT_WRITER: unable to handle more than 1 MFB Region!"
        severity Failure;

    -- ========================================================
    --  Generate break instructions
    -- ========================================================

    instr_gen_i : entity work.PPW_INSTR_GEN
    generic map (
        MVB_ITEMS      => MFB_REGIONS,
        PKT_MTU        => PKT_MTU,
        PCIE_MPS_WIDTH => PCIE_MPS_WIDTH,
        ADDRESS_WIDTH  => ADDRESS_WIDTH,
        PAGE_SIZE      => PAGE_SIZE,
        DEVICE         => DEVICE
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,

        PCIE_MPS       => PCIE_MPS,

        RX_MVB_ADDRESS => RX_MVB_ADDRESS,
        RX_MVB_LENGTH  => RX_MVB_LENGTH,
        RX_MVB_VALID   => RX_MVB_VLD,
        RX_MVB_SRC_RDY => RX_MVB_SRC_RDY,
        RX_MVB_DST_RDY => RX_MVB_DST_RDY,

        TX_MVB_ADDRESS => instr_address,
        TX_MVB_LENGTH  => instr_length,
        TX_MVB_LAST    => instr_last,
        TX_MVB_VALID   => instr_valid,
        TX_MVB_SRC_RDY => instr_src_rdy,
        TX_MVB_DST_RDY => instr_dst_rdy
    );

    -- ========================================================
    --  Packet breaker
    -- ========================================================

    mfb_fifox_i : entity work.MFB_FIFOX
    generic map (
        REGIONS             => MFB_REGIONS,
        REGION_SIZE         => MFB_REGION_SIZE,
        BLOCK_SIZE          => MFB_BLOCK_SIZE,
        ITEM_WIDTH          => MFB_ITEM_WIDTH,
        META_WIDTH          => 0,
        FIFO_DEPTH          => 512,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 0,
        ALMOST_EMPTY_OFFSET => 0
    )
    port map (
        CLK         => CLK,
        RST         => RESET,

        RX_DATA     => RX_MFB_DATA,
        RX_META     => (others => '0'),
        RX_SOF_POS  => RX_MFB_SOF_POS,
        RX_EOF_POS  => RX_MFB_EOF_POS,
        RX_SOF      => RX_MFB_SOF,
        RX_EOF      => RX_MFB_EOF,
        RX_SRC_RDY  => RX_MFB_SRC_RDY,
        RX_DST_RDY  => RX_MFB_DST_RDY,

        TX_DATA     => fifo_tx_mfb_data,
        TX_META     => open,
        TX_SOF_POS  => fifo_tx_mfb_sof_pos,
        TX_EOF_POS  => fifo_tx_mfb_eof_pos,
        TX_SOF      => fifo_tx_mfb_sof,
        TX_EOF      => fifo_tx_mfb_eof,
        TX_SRC_RDY  => fifo_tx_mfb_src_rdy,
        TX_DST_RDY  => fifo_tx_mfb_dst_rdy,

        FIFO_STATUS => open,
        FIFO_AFULL  => open,
        FIFO_AEMPTY => open
    );

    packet_breaker_i : entity work.PPW_PKT_BREAKER
    generic map (
        MFB_REGIONS     => MFB_REGIONS,
        MFB_REGION_SIZE => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
        PKT_MTU         => PKT_MTU,
        ADDRESS_WIDTH   => ADDRESS_WIDTH,
        DEVICE          => DEVICE
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,

        RX_MFB_DATA    => fifo_tx_mfb_data,
        RX_MFB_SOF_POS => fifo_tx_mfb_sof_pos,
        RX_MFB_EOF_POS => fifo_tx_mfb_eof_pos,
        RX_MFB_SOF     => fifo_tx_mfb_sof,
        RX_MFB_EOF     => fifo_tx_mfb_eof,
        RX_MFB_SRC_RDY => fifo_tx_mfb_src_rdy,
        RX_MFB_DST_RDY => fifo_tx_mfb_dst_rdy,

        RX_MVB_ADDRESS => instr_address,
        RX_MVB_LENGTH  => instr_length,
        RX_MVB_LAST    => instr_last,
        RX_MVB_VALID   => instr_valid,
        RX_MVB_SRC_RDY => instr_src_rdy,
        RX_MVB_DST_RDY => instr_dst_rdy,

        TX_MFB_DATA    => TX_MFB_DATA,
        TX_MFB_SOF_POS => TX_MFB_SOF_POS,
        TX_MFB_EOF_POS => TX_MFB_EOF_POS,
        TX_MFB_SOF     => TX_MFB_SOF,
        TX_MFB_EOF     => TX_MFB_EOF,
        TX_MFB_SRC_RDY => TX_MFB_SRC_RDY,
        TX_MFB_DST_RDY => TX_MFB_DST_RDY,

        TX_MVB_ADDRESS => hdrgen_rx_mvb_address,
        TX_MVB_LENGTH  => hdrgen_rx_mvb_length,
        TX_MVB_VALID   => hdrgen_rx_mvb_valid,
        TX_MVB_SRC_RDY => hdrgen_rx_mvb_src_rdy,
        TX_MVB_DST_RDY => hdrgen_rx_mvb_dst_rdy
    );

    -- ========================================================
    --  DMA header generator
    -- ========================================================

    dma_uphdr_gen_i : entity work.PPW_DMA_UPHDR_GEN
    generic map (
        MVB_ITEMS     => MFB_REGIONS,
        PKT_MTU       => PKT_MTU,
        ADDRESS_WIDTH => ADDRESS_WIDTH
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,

        RX_MVB_ADDRESS => hdrgen_rx_mvb_address,
        RX_MVB_LENGTH  => hdrgen_rx_mvb_length,
        RX_MVB_VALID   => hdrgen_rx_mvb_valid,
        RX_MVB_SRC_RDY => hdrgen_rx_mvb_src_rdy,
        RX_MVB_DST_RDY => hdrgen_rx_mvb_dst_rdy,

        TX_MVB_DATA    => TX_MVB_DATA,
        TX_MVB_VLD     => TX_MVB_VLD,
        TX_MVB_SRC_RDY => TX_MVB_SRC_RDY,
        TX_MVB_DST_RDY => TX_MVB_DST_RDY
    );

end architecture;
