-- discard.vhd: Packet (MFB+MVB bus) discarder controlled by a MVB flag.
-- Copyright (C) DynaNIC Semiconductors, Ltd.
-- Author: Jan Privara <privara@dyna-nic.com>, Oct 2025
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- It is implemented using a MFB+MVB splitter with 2 output ports.
-- The second out port is used for discarding the port is not connected, always ready.

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MFB_DISCARDER is
    generic (
        REGIONS          : integer := 4;
        -- MVB
        MVB_ITEM_WIDTH   : integer := 32;
        -- MFB
        MFB_REG_SIZE     : integer := 8;
        MFB_BLOCK_SIZE   : integer := 8;
        MFB_ITEM_WIDTH   : integer := 8;
        -- Size of output MVB FIFOs (in words)
        -- Minimum value is 2!
        OUTPUT_FIFO_SIZE : integer := 32;
        -- Device
        DEVICE           : string  := "ULTRASCALE";

        SPLITTER_FIFOX_MULTI_ARCH : string  := "FULL"
    );    port (
        -- CLOCK AND RESET
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- RX INTERFACE
        RX_MVB_DATA    : in  std_logic_vector(REGIONS*MVB_ITEM_WIDTH-1 downto 0);
        RX_MVB_DISCARD : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MVB_VLD     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MVB_SRC_RDY : in  std_logic;
        RX_MVB_DST_RDY : out std_logic;
        --
        RX_MFB_DATA    : in  std_logic_vector(REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  std_logic_vector(REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;

        -- TX INTERFACE
        TX_MVB_DATA    : out std_logic_vector(REGIONS*MVB_ITEM_WIDTH-1 downto 0);
        TX_MVB_VLD     : out std_logic_vector(REGIONS-1 downto 0);
        TX_MVB_SRC_RDY : out std_logic;
        TX_MVB_DST_RDY : in  std_logic;
        --
        TX_MFB_DATA    : out std_logic_vector(REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MFB_DISCARDER is

    signal split_mvb_data    : slv_array_t(2-1 downto 0)(REGIONS*MVB_ITEM_WIDTH-1 downto 0);
    signal split_mvb_vld     : slv_array_t(2-1 downto 0)(REGIONS-1 downto 0);
    signal split_mvb_src_rdy : std_logic_vector(2-1 downto 0);
    signal split_mvb_dst_rdy : std_logic_vector(2-1 downto 0);

    signal split_mfb_data    : slv_array_t(2-1 downto 0)(REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal split_mfb_sof     : slv_array_t(2-1 downto 0)(REGIONS-1 downto 0);
    signal split_mfb_eof     : slv_array_t(2-1 downto 0)(REGIONS-1 downto 0);
    signal split_mfb_sof_pos : slv_array_t(2-1 downto 0)(REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal split_mfb_eof_pos : slv_array_t(2-1 downto 0)(REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal split_mfb_src_rdy : std_logic_vector(2-1 downto 0);
    signal split_mfb_dst_rdy : std_logic_vector(2-1 downto 0);

begin

    -- MFB splitter - (port 0 is used for dropping)
    dma_mfb_splitter_i : entity work.MFB_SPLITTER_GEN
    generic map (
        SPLITTER_OUTPUTS => 2,
        MVB_ITEMS        => REGIONS,
        MVB_ITEM_WIDTH   => MVB_ITEM_WIDTH,
        MFB_REGIONS      => REGIONS,
        MFB_REG_SIZE     => MFB_REG_SIZE,
        MFB_BLOCK_SIZE   => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH   => MFB_ITEM_WIDTH,
        OUTPUT_FIFO_SIZE => OUTPUT_FIFO_SIZE,
        OUT_PIPE_EN      => false,
        DEVICE           => DEVICE,
        FIFOX_MULTI_ARCH => SPLITTER_FIFOX_MULTI_ARCH
    )
    port map (
        CLK             => CLK,
        RESET           => RESET,

        RX_MVB_DATA     => RX_MVB_DATA,
        RX_MVB_SWITCH   => RX_MVB_DISCARD,
        RX_MVB_PAYLOAD  => (others => '1'),
        RX_MVB_VLD      => RX_MVB_VLD,
        RX_MVB_SRC_RDY  => RX_MVB_SRC_RDY,
        RX_MVB_DST_RDY  => RX_MVB_DST_RDY,

        RX_MFB_DATA     => RX_MFB_DATA,
        RX_MFB_SOF      => RX_MFB_SOF,
        RX_MFB_EOF      => RX_MFB_EOF,
        RX_MFB_SOF_POS  => RX_MFB_SOF_POS,
        RX_MFB_EOF_POS  => RX_MFB_EOF_POS,
        RX_MFB_SRC_RDY  => RX_MFB_SRC_RDY,
        RX_MFB_DST_RDY  => RX_MFB_DST_RDY,

        TX_MVB_DATA     => split_mvb_data,
        TX_MVB_VLD      => split_mvb_vld,
        TX_MVB_SRC_RDY  => split_mvb_src_rdy,
        TX_MVB_DST_RDY  => split_mvb_dst_rdy,

        TX_MFB_DATA     => split_mfb_data,
        TX_MFB_SOF      => split_mfb_sof,
        TX_MFB_EOF      => split_mfb_eof,
        TX_MFB_SOF_POS  => split_mfb_sof_pos,
        TX_MFB_EOF_POS  => split_mfb_eof_pos,
        TX_MFB_SRC_RDY  => split_mfb_src_rdy,
        TX_MFB_DST_RDY  => split_mfb_dst_rdy
    );

    -- port 1 is used for packet discarding - not connected, always ready
    split_mfb_dst_rdy(1) <= '1';
    split_mvb_dst_rdy(1) <= '1';

    -- output interface - port 0
    TX_MVB_DATA          <= split_mvb_data(0);
    TX_MVB_VLD           <= split_mvb_vld(0);
    TX_MVB_SRC_RDY       <= split_mvb_src_rdy(0);
    split_mvb_dst_rdy(0) <= TX_MVB_DST_RDY;

    TX_MFB_DATA          <= split_mfb_data(0);
    TX_MFB_SOF           <= split_mfb_sof(0);
    TX_MFB_EOF           <= split_mfb_eof(0);
    TX_MFB_SOF_POS       <= split_mfb_sof_pos(0);
    TX_MFB_EOF_POS       <= split_mfb_eof_pos(0);
    TX_MFB_SRC_RDY       <= split_mfb_src_rdy(0);
    split_mfb_dst_rdy(0) <= TX_MFB_DST_RDY;

end architecture;
