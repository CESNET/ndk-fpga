-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Mario Kuka <kuka@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of testbench is
    constant CLK_PER    : time := 1.0 ns;
    constant RESET_TIME : time := 5.2 ns;

    signal clk   : std_logic;
    signal reset : std_logic;

    constant DATA_WIDTH    : integer := 512;
    constant SOP_POS_WIDTH : integer := 3;
    constant CHANNEL_WIDTH : integer := 8;

    signal RX_CHANNEL : std_logic_vector(CHANNEL_WIDTH-1 downto 0);
    signal RX_DATA    : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal RX_SOP_POS : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
    signal RX_EOP_POS : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
    signal RX_SOP     : std_logic;
    signal RX_EOP     : std_logic;
    signal RX_SRC_RDY : std_logic;
    signal RX_DST_RDY : std_logic;

    signal TX_HDR     : std_logic_vector(8*8+CHANNEL_WIDTH-1 downto 0);
    signal TX_DATA    : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal TX_SOP_POS : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
    signal TX_EOP_POS : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
    signal TX_SOP     : std_logic;
    signal TX_EOP     : std_logic;
    signal TX_SRC_RDY : std_logic;
    signal TX_DST_RDY : std_logic;
begin

    -- -------------------------------------------------------------------------
    --                        clk and reset generators
    -- -------------------------------------------------------------------------

    -- generating dcpro_clk
    clk_gen: process
    begin
        clk <= '1';
        wait for CLK_PER / 2;
        clk <= '0';
        wait for CLK_PER / 2;
    end process clk_gen;

    -- generating dcpro_reset
    reset_gen: process
    begin
        reset <= '1';
        wait for RESET_TIME;
        reset <= '0';
        wait;
    end process reset_gen;

    -- -------------------------------------------------------------------------
    --                              UUT
    -- -------------------------------------------------------------------------
    uut : entity work.DMA_HDR_EXTRACTOR
    generic map(
        DATA_WIDTH    => DATA_WIDTH,
        SOP_POS_WIDTH => SOP_POS_WIDTH,
        CHANNEL_WIDTH => CHANNEL_WIDTH
    )
    port map(
        CLK         => clk,
        RESET       => reset,
        RX_CHANNEL  =>RX_CHANNEL,
        RX_DATA     =>RX_DATA,
        RX_SOP_POS  =>RX_SOP_POS,
        RX_EOP_POS  =>RX_EOP_POS,
        RX_SOP      =>RX_SOP,
        RX_EOP      =>RX_EOP,
        RX_SRC_RDY  =>RX_SRC_RDY,
        RX_DST_RDY  =>RX_DST_RDY,
        TX_HDR      =>TX_HDR,
        TX_DATA     =>TX_DATA,
        TX_SOP_POS  =>TX_SOP_POS,
        TX_EOP_POS  =>TX_EOP_POS,
        TX_SOP      =>TX_SOP,
        TX_EOP      =>TX_EOP,
        TX_SRC_RDY  =>TX_SRC_RDY,
        TX_DST_RDY  =>TX_DST_RDY
    );

   -- -------------------------------------------------------------------------
   --                          Testbench process
   -- -------------------------------------------------------------------------

   tb: process
   begin
        TX_DST_RDY <= '1';
        RX_SRC_RDY <= '0';
        RX_CHANNEL <= X"EE";
        RX_EOP_POS <= (others => '1');
        RX_DATA(1*64-1 downto 0*64) <= X"1111111111111111";
        RX_DATA(2*64-1 downto 1*64) <= X"2222222222222222";
        RX_DATA(3*64-1 downto 2*64) <= X"3333333333333333";
        RX_DATA(4*64-1 downto 3*64) <= X"4444444444444444";
        RX_DATA(5*64-1 downto 4*64) <= X"5555555555555555";
        RX_DATA(6*64-1 downto 5*64) <= X"6666666666666666";
        RX_DATA(7*64-1 downto 6*64) <= X"7777777777777777";
        RX_DATA(8*64-1 downto 7*64) <= X"8888888888888888";
        wait for reset_time;

        RX_SRC_RDY <= '1';
        RX_SOP_POS <= std_logic_vector(to_unsigned(0, SOP_POS_WIDTH));
        RX_SOP     <= '1';
        RX_EOP     <= '0';
        wait for clk_per;

        RX_SRC_RDY <= '1';
        RX_SOP_POS <= std_logic_vector(to_unsigned(0, SOP_POS_WIDTH));
        RX_SOP     <= '0';
        RX_EOP     <= '1';
        wait for clk_per;

        RX_SRC_RDY <= '0';
        RX_SOP_POS <= std_logic_vector(to_unsigned(0, SOP_POS_WIDTH));
        RX_SOP     <= '0';
        RX_EOP     <= '0';
        wait for clk_per;

        RX_SRC_RDY <= '1';
        RX_SOP_POS <= std_logic_vector(to_unsigned(7, SOP_POS_WIDTH));
        RX_SOP     <= '1';
        RX_EOP     <= '0';
        wait for clk_per;

        RX_SRC_RDY <= '0';
        RX_SOP_POS <= std_logic_vector(to_unsigned(7, SOP_POS_WIDTH));
        RX_DATA    <= (others => '0');
        RX_CHANNEL <= (others => '0');
        RX_SOP     <= '0';
        RX_EOP     <= '0';
        wait for clk_per;

        RX_SRC_RDY <= '1';
        RX_SOP_POS <= std_logic_vector(to_unsigned(0, SOP_POS_WIDTH));
        RX_DATA    <= (others => '0');
        RX_CHANNEL <= (others => '0');
        RX_SOP     <= '0';
        RX_EOP     <= '1';
        wait for clk_per;

        RX_SRC_RDY <= '0';
        RX_SOP_POS <= std_logic_vector(to_unsigned(0, SOP_POS_WIDTH));
        RX_SOP     <= '0';
        RX_EOP     <= '0';
        wait for clk_per;
        wait;
    end process;
end architecture behavioral;
