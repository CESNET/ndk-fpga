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
    constant CLK_PERIOD : time := 10 ns;

    -- clk, reset signals
    signal reset : std_logic := '0';
    signal clk   : std_logic := '0';

    -- input interface signals
    signal rx_data    : std_logic_vector(511 downto 0);
    signal rx_sop     : std_logic_vector(3 downto 0) := "1001";
    signal rx_eop     : std_logic_vector(3 downto 0) := "1010";
    signal rx_sop_pos : std_logic_vector(7 downto 0) := "01101100";
    signal rx_eop_pos : std_logic_vector(15 downto 0) := "1111000011000011";
    signal rx_src_rdy : std_logic := '0';
    signal tx_dst_rdy : std_logic := '0';

    -- output interface signals
    signal tx_data    : std_logic_vector(127 downto 0);
    signal tx_sop     : std_logic_vector(0 downto 0);
    signal tx_eop     : std_logic_vector(0 downto 0);
    signal tx_sop_pos : std_logic_vector(1 downto 0);
    signal tx_eop_pos : std_logic_vector(3 downto 0);
    signal tx_src_rdy : std_logic;
    signal rx_dst_rdy : std_logic;

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
        RESET => reset,
        CLK   => clk,

        RX_DATA    => rx_data,
        RX_SOP     => rx_sop,
        RX_EOP     => rx_eop,
        RX_SOP_POS => rx_sop_pos,
        RX_EOP_POS => rx_eop_pos,
        RX_SRC_RDY => rx_src_rdy,
        RX_DST_RDY => rx_dst_rdy,

        TX_DATA    => tx_data,
        TX_SOP     => tx_sop,
        TX_EOP     => tx_eop,
        TX_SOP_POS => tx_sop_pos,
        TX_EOP_POS => tx_eop_pos,
        TX_SRC_RDY => tx_src_rdy,
        TX_DST_RDY => tx_dst_rdy
    );

    -- cllock process
    clk_p : process
    begin
        clk <= '0';
        wait for CLK_PERIOD/2;
        clk <= '1';
        wait for CLK_PERIOD/2;
    end process;

    -- stimulus process
    stim_p : process
    begin
        wait for 100 ns;

        rx_data <= DATA_1;
        wait for CLK_PERIOD*4;

        rx_src_rdy <= '1';
        wait for CLK_PERIOD;

        rx_src_rdy <= '0';
        reset      <= '1' after CLK_PERIOD*4, '0' after CLK_PERIOD*5;
        tx_dst_rdy <= '1', '0' after CLK_PERIOD*2, '1' after CLK_PERIOD*3, '0' after CLK_PERIOD*6;
        wait for CLK_PERIOD*10;

        rx_data    <= DATA_2;
        rx_src_rdy <= '1';
        wait for CLK_PERIOD*2;

        rx_data    <= DATA_1;
        tx_dst_rdy <= '1', '0' after CLK_PERIOD*5;
        wait;
    end process;

end architecture;
