-- testbench.vhd: Testbench for MFB transformer component
-- Copyright (C) 2020 CESNET
-- Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>

-- SPDX-License-Identifier: BSD-3-Clause
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
-- library containing log2 function
use work.math_pack.all;

entity TESTBENCH is
end entity;

architecture FULL of TESTBENCH is

    -- test data
    constant DATA_1 : std_logic_vector(511 downto 0) := (511 => '1', 500 => '1', 255 => '1', others => '0');
    constant DATA_2 : std_logic_vector(511 downto 0) := ('0', '1', '1', '1', others => '0');

    -- clock period definition
    constant CLK_period : time := 10 ns;

    -- clk, reset signals
    signal RESET : std_logic := '0';
    signal CLK   : std_logic := '0';

    -- input interface signals
    signal RX_DATA    : std_logic_vector(511 downto 0);
    signal RX_SOP     : std_logic_vector(3 downto 0) := "1001";
    signal RX_EOP     : std_logic_vector(3 downto 0) := "1010";
    signal RX_SOP_POS : std_logic_vector(7 downto 0) := "01101100";
    signal RX_EOP_POS : std_logic_vector(15 downto 0) := "1111000011000011";
    signal RX_SRC_RDY : std_logic := '0';
    signal TX_DST_RDY : std_logic := '0';

    -- output interface signals
    signal TX_DATA    : std_logic_vector(127 downto 0);
    signal TX_SOP     : std_logic_vector(0 downto 0);
    signal TX_EOP     : std_logic_vector(0 downto 0);
    signal TX_SOP_POS : std_logic_vector(1 downto 0);
    signal TX_EOP_POS : std_logic_vector(3 downto 0);
    signal TX_SRC_RDY : std_logic;
    signal RX_DST_RDY : std_logic;

begin

    -- instantiate the unit under test (UUT)
    uut_i: entity work.MFB_TRANSFORMER
    generic map (
        RX_REGIONS  => 4,
        TX_REGIONS  => 1,
        REGION_SIZE => 4,
        BLOCK_SIZE  => 4,
        ITEM_WIDTH  => 8
    )
    port map (
        RESET => RESET,
        CLK   => CLK,

        RX_DATA    => RX_DATA,
        RX_SOP     => RX_SOP,
        RX_EOP     => RX_EOP,
        RX_SOP_POS => RX_SOP_POS,
        RX_EOP_POS => RX_EOP_POS,
        RX_SRC_RDY => RX_SRC_RDY,
        RX_DST_RDY => RX_DST_RDY,

        TX_DATA    => TX_DATA,
        TX_SOP     => TX_SOP,
        TX_EOP     => TX_EOP,
        TX_SOP_POS => TX_SOP_POS,
        TX_EOP_POS => TX_EOP_POS,
        TX_SRC_RDY => TX_SRC_RDY,
        TX_DST_RDY => TX_DST_RDY
    );

    -- cllock process
    CLK_p : process
    begin
        CLK <= '0';
        wait for CLK_period/2;
        CLK <= '1';
        wait for CLK_period/2;
    end process;

    -- stimulus process
    stim_p : process
    begin
        wait for 100 ns;

        RX_DATA <= DATA_1;
        wait for CLK_period*4;

        RX_SRC_RDY <= '1';
        wait for CLK_period;

        RX_SRC_RDY <= '0';
        RESET <= '1' after CLK_period*4, '0' after CLK_period*5;
        TX_DST_RDY <= '1', '0' after CLK_period*2, '1' after CLK_period*3, '0' after CLK_period*6;
        wait for CLK_period*10;

        RX_DATA <= DATA_2;
        RX_SRC_RDY <= '1';
        wait for CLK_period*2;

        RX_DATA <= DATA_1;
        TX_DST_RDY <= '1', '0' after CLK_period*5;
        wait;
    end process;

end architecture;
