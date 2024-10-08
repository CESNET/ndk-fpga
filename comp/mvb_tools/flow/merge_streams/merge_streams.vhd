-- merge_streams.vhd: Merge multiple MVB streams to single MVB stream
-- Copyright (C) 2023 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The MVB_MERGE_STREAMS component is used to merge two or more independent MVB
-- streams into one. The order of merging items is random. The speed of
-- switching between input streams can be influenced by the width of the timeout
-- signal (parameter SW_TIMEOUT_W). Better transmission efficiency can be
-- achieved by enabling input MVB SHAKEDOWNS (parameter RX_SHAKEDOWN_EN).
--
entity MVB_MERGE_STREAMS is
    generic(
        -- Number of MVB items
        MVB_ITEMS       : natural := 4;
        -- MVB item width in bits
        MVB_ITEM_WIDTH  : natural := 32;
        -- Number of input MVB streams, must be power of two
        RX_STREAMS      : natural := 2;
        -- Enable MVB SHAKEDOWN on each MVB input stream
        RX_SHAKEDOWN_EN : boolean := True;
        -- Width of timeout counter, determines the time when the switch to
        -- the next active MVB stream occurs
        SW_TIMEOUT_W    : natural := 4;
        -- FPGA device string
        DEVICE          : string := "AGILEX"
    );
    port(
        -- Clock input
        CLK        : in  std_logic;
        -- Reset input synchronized with CLK
        RESET      : in  std_logic;

        -- RX MVB: data word with MVB items
        RX_DATA    : in  slv_array_t(RX_STREAMS-1 downto 0)(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- RX MVB: valid of each MVB item
        RX_VLD     : in  slv_array_t(RX_STREAMS-1 downto 0)(MVB_ITEMS-1 downto 0);
        -- RX MVB: source ready
        RX_SRC_RDY : in  std_logic_vector(RX_STREAMS-1 downto 0);
        -- RX MVB: destination ready
        RX_DST_RDY : out std_logic_vector(RX_STREAMS-1 downto 0);

        -- TX MVB: data word with MVB items
        TX_DATA    : out std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- TX MVB: valid of each MVB item
        TX_VLD     : out std_logic_vector(MVB_ITEMS-1 downto 0);
        -- TX MVB: source ready
        TX_SRC_RDY : out std_logic;
        -- TX MVB: destination ready
        TX_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MVB_MERGE_STREAMS is

    signal s_shake_tx_data    : slv_array_t(RX_STREAMS-1 downto 0)(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    signal s_shake_tx_vld     : slv_array_t(RX_STREAMS-1 downto 0)(MVB_ITEMS-1 downto 0);
    signal s_shake_tx_next    : slv_array_t(RX_STREAMS-1 downto 0)(MVB_ITEMS-1 downto 0);
    signal s_shake_tx_src_rdy : std_logic_vector(RX_STREAMS-1 downto 0);
    signal s_shake_tx_dst_rdy : std_logic_vector(RX_STREAMS-1 downto 0);

    signal s_stream_enable    : std_logic_vector(RX_STREAMS-1 downto 0);
    signal s_mux_sel          : unsigned(log2(RX_STREAMS)-1 downto 0);
    signal s_mux_sel_en       : std_logic;
    signal s_mux_sel_inc      : unsigned(log2(RX_STREAMS)-1 downto 0);

    signal s_mux_tx_data      : std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    signal s_mux_tx_vld       : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal s_mux_tx_src_rdy   : std_logic;
    signal s_mux_tx_dst_rdy   : std_logic;

    signal s_timeout_rst      : std_logic;
    signal s_timeout_en       : std_logic;
    signal s_timeout_cnt      : unsigned(SW_TIMEOUT_W-1 downto 0);
    signal s_timeout          : std_logic;

begin

    -- -------------------------------------------------------------------------
    -- INPUT STAGE WITH OPTIONAL MVB_SHAKEDOWN
    -- -------------------------------------------------------------------------

    rx_g: for ii in 0 to RX_STREAMS-1 generate
        shake_g: if RX_SHAKEDOWN_EN generate
            shake_i : entity work.MVB_SHAKEDOWN
            generic map(
                RX_ITEMS    => MVB_ITEMS,
                TX_ITEMS    => MVB_ITEMS,
                ITEM_WIDTH  => MVB_ITEM_WIDTH,
                SHAKE_PORTS => 2
            )
            port map(
                CLK        => CLK,
                RESET      => RESET,

                RX_DATA    => RX_DATA(ii),
                RX_VLD     => RX_VLD(ii),
                RX_SRC_RDY => RX_SRC_RDY(ii),
                RX_DST_RDY => RX_DST_RDY(ii),

                TX_DATA    => s_shake_tx_data(ii),
                TX_VLD     => s_shake_tx_vld(ii),
                TX_NEXT    => s_shake_tx_next(ii)
            );

            s_shake_tx_src_rdy(ii) <= or s_shake_tx_vld(ii);
            s_shake_tx_next(ii)    <= (others => s_shake_tx_dst_rdy(ii));

        else generate
            s_shake_tx_data(ii)    <= RX_DATA(ii);
            s_shake_tx_vld(ii)     <= RX_VLD(ii);
            s_shake_tx_src_rdy(ii) <= RX_SRC_RDY(ii);
            RX_DST_RDY(ii)         <= s_shake_tx_dst_rdy(ii);

        end generate;
    end generate;

    -- -------------------------------------------------------------------------
    -- DATA MULTIPLEXORS AND OUTPUT REGISTER
    -- -------------------------------------------------------------------------

    s_mux_tx_data      <= s_shake_tx_data(to_integer(s_mux_sel));
    s_mux_tx_vld       <= s_shake_tx_vld(to_integer(s_mux_sel));
    s_mux_tx_src_rdy   <= s_shake_tx_src_rdy(to_integer(s_mux_sel));
    s_shake_tx_dst_rdy <= s_mux_tx_dst_rdy and s_stream_enable;

    s_mux_tx_dst_rdy <= TX_DST_RDY;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_DST_RDY = '1') then
                TX_DATA    <= s_mux_tx_data;
                TX_VLD     <= s_mux_tx_vld;
                TX_SRC_RDY <= s_mux_tx_src_rdy;
            end if;
            if (RESET = '1') then
                TX_SRC_RDY <= '0';
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    -- CONTROL LOGIC WITH TIMEOUT AND NEXT STREAM DETECTION
    -- -------------------------------------------------------------------------

    -- This process searches for the nearest next MVB stream with a valid source
    -- ready and calculates the necessary increment to shift the select signal.
    process (all)
        variable v_mux_sel_inc : unsigned(log2(RX_STREAMS)-1 downto 0);
        variable v_mux_sel_new : unsigned(log2(RX_STREAMS)-1 downto 0);
    begin
        v_mux_sel_inc := to_unsigned(1, v_mux_sel_inc'length);
        for ii in 0 to RX_STREAMS-1 loop
            v_mux_sel_new := s_mux_sel + v_mux_sel_inc;
            if (s_shake_tx_src_rdy(to_integer(v_mux_sel_new)) = '1') then
                exit;
            end if;
            v_mux_sel_inc := v_mux_sel_inc + 1;
        end loop;
        s_mux_sel_inc <= v_mux_sel_inc;
    end process;

    -- Switching of the operated input streams occurs in the case of exceeding
    -- the timeout or when there is no longer a valid source ready signal on
    -- the current stream.
    s_mux_sel_en <= s_timeout or (not s_mux_tx_src_rdy and s_mux_tx_dst_rdy);

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                s_mux_sel <= (others => '0');
            elsif (s_mux_sel_en = '1') then
                s_mux_sel <= s_mux_sel + s_mux_sel_inc;
            end if;
        end if;
    end process;

    process (all)
    begin
        s_stream_enable <= (others => '0');
        for ii in 0 to RX_STREAMS-1 loop
            if (s_mux_sel = ii) then
                s_stream_enable(ii) <= '1';
            end if;
        end loop;
    end process;

    -- The timeout counter counts the number of transmitted valid words within
    -- one uninterrupted service of the selected input stream.
    s_timeout_rst <= RESET or s_mux_sel_en;
    s_timeout_en <= s_mux_tx_src_rdy and s_mux_tx_dst_rdy;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_timeout_rst = '1') then
                s_timeout_cnt <= (others => '0');
            elsif (s_timeout_en = '1' and s_timeout = '0') then
                s_timeout_cnt <= s_timeout_cnt + 1;
            end if;
        end if;
    end process;

    s_timeout <= s_timeout_cnt(SW_TIMEOUT_W-1);

end architecture;
