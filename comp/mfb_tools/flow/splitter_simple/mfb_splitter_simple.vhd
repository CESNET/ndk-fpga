-- mfb_splitter_simple.vhd: This component transmits recieved packets on one interface to one out of the two outputs accaoring to the select bit.
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
-- TODO? : RESETS and OUTPUT REGISTERS

-- This component transmits received packets on one interface to one out of the two outputs according to the select bit.
entity MFB_SPLITTER_SIMPLE is
    generic (
        -- number of regions in a data word
        REGIONS         : natural := 2;
        -- number of blocks in a region
        REGION_SIZE     : natural := 8;
        -- number of items in a block
        BLOCK_SIZE      : natural := 8;
        -- number of bits in an item
        ITEM_WIDTH      : natural := 8;
        -- number of bits for metadata in a single region
        META_WIDTH      : natural := 8
    );
    port (
        CLK             : in  std_logic;
        RST             : in  std_logic;

        -- ==============
        -- rx interface
        -- ==============

        -- is only valid with asserted sof signal
        RX_MFB_SEL      : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_DATA     : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_MFB_META     : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        RX_MFB_SOF      : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_EOF      : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_SOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS  : in  std_logic_vector(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        RX_MFB_SRC_RDY  : in  std_logic;
        RX_MFB_DST_RDY  : out std_logic;

        -- ==============
        -- tx interface 0
        -- ==============

        TX0_MFB_DATA    : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX0_MFB_META    : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        TX0_MFB_SOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX0_MFB_EOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX0_MFB_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX0_MFB_EOF_POS : out std_logic_vector(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        TX0_MFB_SRC_RDY : out std_logic;
        TX0_MFB_DST_RDY : in  std_logic;

        -- ==============
        -- tx interface 1
        -- ==============

        TX1_MFB_DATA    : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX1_MFB_META    : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        TX1_MFB_SOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX1_MFB_EOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX1_MFB_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX1_MFB_EOF_POS : out std_logic_vector(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        TX1_MFB_SRC_RDY : out std_logic;
        TX1_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture BEHAV of MFB_SPLITTER_SIMPLE is

    constant SOF_POS_WIDTH : natural := max(1,log2(REGION_SIZE));
    constant EOF_POS_WIDTH : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));
    constant DATA_WIDTH    : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;

    signal spl_rx_eof_pos : std_logic_vector(REGIONS*EOF_POS_WIDTH-1 downto 0);

    signal spl_tx_data    : slv_array_t     (2-1 downto 0)(DATA_WIDTH-1 downto 0);
    signal spl_tx_meta    : slv_array_t     (2-1 downto 0)(REGIONS*META_WIDTH-1 downto 0);
    signal spl_tx_sof     : slv_array_t     (2-1 downto 0)(REGIONS-1 downto 0);
    signal spl_tx_eof     : slv_array_t     (2-1 downto 0)(REGIONS-1 downto 0);
    signal spl_tx_sof_pos : slv_array_t     (2-1 downto 0)(REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal spl_tx_eof_pos : slv_array_t     (2-1 downto 0)(REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal spl_tx_src_rdy : std_logic_vector(2-1 downto 0);
    signal spl_tx_dst_rdy : std_logic_vector(2-1 downto 0);

begin

    -- The EOF_POS ports of this entity are empty when a Region holds one Item.
    -- MFB_SPLITTER_SIMPLE_GEN keeps one bit per Region even then.
    eof_pos_g : if (log2(REGION_SIZE*BLOCK_SIZE) > 0) generate
        spl_rx_eof_pos  <= RX_MFB_EOF_POS;
        TX0_MFB_EOF_POS <= spl_tx_eof_pos(0);
        TX1_MFB_EOF_POS <= spl_tx_eof_pos(1);
    else generate
        spl_rx_eof_pos  <= (others => '0');
    end generate;

    splitter_i : entity work.MFB_SPLITTER_SIMPLE_GEN
    generic map (
        SPLITTER_OUTPUTS => 2,
        REGIONS          => REGIONS,
        REGION_SIZE      => REGION_SIZE,
        BLOCK_SIZE       => BLOCK_SIZE,
        ITEM_WIDTH       => ITEM_WIDTH,
        META_WIDTH       => META_WIDTH
    )
    port map (
        CLK            => CLK,
        RESET          => RST,

        RX_MFB_SEL     => RX_MFB_SEL,
        RX_MFB_DATA    => RX_MFB_DATA,
        RX_MFB_META    => RX_MFB_META,
        RX_MFB_SOF     => RX_MFB_SOF,
        RX_MFB_EOF     => RX_MFB_EOF,
        RX_MFB_SOF_POS => RX_MFB_SOF_POS,
        RX_MFB_EOF_POS => spl_rx_eof_pos,
        RX_MFB_SRC_RDY => RX_MFB_SRC_RDY,
        RX_MFB_DST_RDY => RX_MFB_DST_RDY,

        TX_MFB_DATA    => spl_tx_data,
        TX_MFB_META    => spl_tx_meta,
        TX_MFB_SOF     => spl_tx_sof,
        TX_MFB_EOF     => spl_tx_eof,
        TX_MFB_SOF_POS => spl_tx_sof_pos,
        TX_MFB_EOF_POS => spl_tx_eof_pos,
        TX_MFB_SRC_RDY => spl_tx_src_rdy,
        TX_MFB_DST_RDY => spl_tx_dst_rdy
    );

    TX0_MFB_DATA      <= spl_tx_data(0);
    TX0_MFB_META      <= spl_tx_meta(0);
    TX0_MFB_SOF       <= spl_tx_sof(0);
    TX0_MFB_EOF       <= spl_tx_eof(0);
    TX0_MFB_SOF_POS   <= spl_tx_sof_pos(0);
    TX0_MFB_SRC_RDY   <= spl_tx_src_rdy(0);
    spl_tx_dst_rdy(0) <= TX0_MFB_DST_RDY;

    TX1_MFB_DATA      <= spl_tx_data(1);
    TX1_MFB_META      <= spl_tx_meta(1);
    TX1_MFB_SOF       <= spl_tx_sof(1);
    TX1_MFB_EOF       <= spl_tx_eof(1);
    TX1_MFB_SOF_POS   <= spl_tx_sof_pos(1);
    TX1_MFB_SRC_RDY   <= spl_tx_src_rdy(1);
    spl_tx_dst_rdy(1) <= TX1_MFB_DST_RDY;

end architecture;
