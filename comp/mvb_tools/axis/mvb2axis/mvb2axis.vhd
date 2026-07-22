-- mvb2axi.vhd: MVB to AXIS convertor
-- Copyright (C) 2026 Dynanic Semiconductors Ltd.
-- Author(s): David Beneš <benes@dyna-nic.com>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Converts MVB interface to AXI-stream
-- Covers 3 cases:
--      * MVB_ITEM_WIDTH > TDATA_WIDTH -- Sends multi-beat AXIS transaction
--      * MVB_ITEM_WIDTH < TDATA_WIDTH -- Lower bits are filled with MVB, the rest is zeroed out
--      * MVB_ITEM_WIDTH = TDATA_WIDTH -- 1:1 mapping
-- MVB_META input is translated to TUSER
-- TUSER remains valid and constant across all data beats of a single packet (from the first beat until TLAST is asserted).
entity MVB2AXIS is
    generic (
        -- Number of MVB items, any positive
        ITEMS       : natural := 4;
        -- MVB item width, must be multiple of 8
        ITEM_WIDTH  : natural := 288;
        -- META signal translated to tuser signal, any positive
        META_WIDTH  : natural := 64;
        -- AXI data width, must by multiple of 8
        TDATA_WIDTH : natural := 256
    );
    port (
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK : in std_logic;
        RST : in std_logic;

        -- =====================================================================
        -- INPUT MVB INTERFACE
        -- =====================================================================
        RX_MVB_DATA     : in  std_logic_vector(ITEMS*ITEM_WIDTH - 1 downto 0);
        RX_MVB_META     : in  std_logic_vector(ITEMS*META_WIDTH - 1 downto 0) := (others => '0');
        RX_MVB_VLD      : in  std_logic_vector(ITEMS            - 1 downto 0);
        RX_MVB_SRC_RDY  : in  std_logic;
        RX_MVB_DST_RDY  : out std_logic;

        -- =====================================================================
        -- OUTPUT AXIS INTERFACE
        -- =====================================================================
        TX_AXIS_TDATA   : out std_logic_vector(TDATA_WIDTH - 1 downto 0);
        TX_AXIS_TUSER   : out std_logic_vector(META_WIDTH  - 1 downto 0);
        TX_AXIS_TKEEP   : out std_logic_vector((TDATA_WIDTH)/8-1 downto 0);
        TX_AXIS_TLAST   : out std_logic;
        TX_AXIS_TVALID  : out std_logic;
        TX_AXIS_TREADY  : in  std_logic
    );
end entity;

architecture FULL of MVB2AXIS is

    signal seq_tx_data      : std_logic_vector(ITEM_WIDTH - 1 downto 0);
    signal seq_tx_meta      : std_logic_vector(META_WIDTH - 1 downto 0);
    signal seq_tx_vld       : std_logic_vector(1          - 1 downto 0);
    signal seq_tx_src_rdy   : std_logic;
    signal seq_tx_dst_rdy   : std_logic;

begin
    sequencer_i: entity work.MVB_SERIALIZER
    generic map (
        ITEMS       => ITEMS,
        ITEM_WIDTH  => ITEM_WIDTH,
        META_WIDTH  => META_WIDTH
    )
    port map (
        CLK => CLK,
        RST => RST,

        RX_MVB_DATA     => RX_MVB_DATA,
        RX_MVB_META     => RX_MVB_META,
        RX_MVB_VLD      => RX_MVB_VLD,
        RX_MVB_SRC_RDY  => RX_MVB_SRC_RDY,
        RX_MVB_DST_RDY  => RX_MVB_DST_RDY,

        TX_MVB_DATA     => seq_tx_data,
        TX_MVB_META     => seq_tx_meta,
        TX_MVB_VLD      => seq_tx_vld,
        TX_MVB_SRC_RDY  => seq_tx_src_rdy,
        TX_MVB_DST_RDY  => seq_tx_dst_rdy
    );

    -- =========================================================================
    -- Equal Width of input MVB and output AXIS
    -- =========================================================================
    equal_widths_g: if ITEM_WIDTH = TDATA_WIDTH generate
    begin
        TX_AXIS_TDATA   <= seq_tx_data;
        TX_AXIS_TUSER   <= seq_tx_meta;
        TX_AXIS_TKEEP   <= (others => '1');
        TX_AXIS_TLAST   <= '1';
        TX_AXIS_TVALID  <= seq_tx_src_rdy and seq_tx_vld(0);
        seq_tx_dst_rdy  <= TX_AXIS_TREADY;
    end generate;

    -- =========================================================================
    -- MVB Item is smaller than AXIS bus (Zero Padding)
    -- =========================================================================
    mvb_smaller_g: if ITEM_WIDTH < TDATA_WIDTH generate
    begin
        -- Map data to LSBs, zero-pad the rest
        TX_AXIS_TDATA(ITEM_WIDTH - 1 downto 0)             <= seq_tx_data;
        TX_AXIS_TDATA(TDATA_WIDTH - 1 downto ITEM_WIDTH)   <= (others => '0');

        TX_AXIS_TUSER   <= seq_tx_meta;

        -- Set Keep high only for valid lower bytes
        TX_AXIS_TKEEP((ITEM_WIDTH / 8) - 1 downto 0)             <= (others => '1');
        TX_AXIS_TKEEP((TDATA_WIDTH / 8) - 1 downto ITEM_WIDTH/8) <= (others => '0');

        TX_AXIS_TLAST   <= '1';
        TX_AXIS_TVALID  <= seq_tx_src_rdy and seq_tx_vld(0);
        seq_tx_dst_rdy  <= TX_AXIS_TREADY;
    end generate;

    -- =========================================================================
    -- MVB Item is larger than AXIS bus (Multi-Beat Serialization)
    -- =========================================================================
    axis_smaller_g: if ITEM_WIDTH > TDATA_WIDTH generate
        constant TX_BEATS        : natural := (ITEM_WIDTH + TDATA_WIDTH - 1) / TDATA_WIDTH; -- floors itself
        constant LAST_BEAT_BYTES : natural := (ITEM_WIDTH / 8) - ((TX_BEATS - 1) * (TDATA_WIDTH / 8));
        constant PADDED_WIDTH    : natural := TX_BEATS * TDATA_WIDTH;

        signal cnt_beat       : unsigned(log2(TX_BEATS) - 1 downto 0) := (others => '0');
        signal padded_tx_data : std_logic_vector(PADDED_WIDTH - 1 downto 0);
        signal is_last_beat   : std_logic;
        signal internal_valid : std_logic;
    begin

        padded_tx_data(ITEM_WIDTH - 1 downto 0)            <= seq_tx_data;
        padded_tx_data(PADDED_WIDTH - 1 downto ITEM_WIDTH) <= (others => '0');

        internal_valid <= seq_tx_src_rdy and seq_tx_vld(0);
        is_last_beat   <= '1' when (cnt_beat = TX_BEATS - 1) else '0';

        -- AXI Output logic
        TX_AXIS_TVALID <= internal_valid;
        TX_AXIS_TLAST  <= is_last_beat;
        TX_AXIS_TDATA  <= padded_tx_data((to_integer(cnt_beat) + 1)*TDATA_WIDTH - 1 downto to_integer(cnt_beat)*TDATA_WIDTH);
        TX_AXIS_TUSER  <= seq_tx_meta;

        -- TKEEP Logic: full 1s unless it's the final fractional beat
        process (all)
        begin
            if (is_last_beat = '1') then
                TX_AXIS_TKEEP                               <= (others => '0');
                TX_AXIS_TKEEP(LAST_BEAT_BYTES - 1 downto 0) <= (others => '1');
            else
                TX_AXIS_TKEEP <= (others => '1');
            end if;
        end process;

        -- FIFO Read Logic: Only pop from FIFO when the last beat is successfully handshaked
        seq_tx_dst_rdy <= TX_AXIS_TREADY when (is_last_beat = '1' and internal_valid = '1') else '0';

        -- Beat Counter State Machine
        process (all)
        begin
            if rising_edge(CLK) then
                if (RST = '1') then
                    cnt_beat <= (others => '0');
                elsif (internal_valid = '1' and TX_AXIS_TREADY = '1') then
                    if (is_last_beat = '1') then
                        cnt_beat <= (others => '0');
                    else
                        cnt_beat <= cnt_beat + 1;
                    end if;
                end if;
            end if;
        end process;

    end generate;

end architecture;
