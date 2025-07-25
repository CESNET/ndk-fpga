--! testbench.vhd: Testbench for BRAM_XILINX
--! # Copyright (C) 2015 CESNET
--! # Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
--! SPDX-License-Identifier: BSD-3-Clause
--
--! $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

entity TESTBENCH is

end entity;

architecture BEHAVIORAL of TESTBENCH is

    constant CLKPER            : time := 10 ns;           -- Clock period
    constant RESET_TIME        : time := 2*CLKPER + 5 ns; -- Reset duration
    constant DATA_WIDTH        : integer := 37;
    constant ADDRESS_WIDTH     : integer := 12;
    constant BRAM_TYPE         : integer := 36;
    constant ENABLE_OUT_REG    : boolean := true;
    constant DEVICE            : string := "ULTRASCALE";

    --! Clock and reset signals
    signal clk       : std_logic;
    signal reset     : std_logic;
    signal pipe_en   : std_logic;
    signal re        : std_logic;
    signal we        : std_logic;
    signal addr      : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
    signal di        : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal do_dv     : std_logic;
    signal do        : std_logic_vector(DATA_WIDTH-1 downto 0);
begin

    --! BRAM_XILINX
    uut : entity work.SP_BRAM_XILINX
    generic map (
        --! Input data width
        DATA_WIDTH     => DATA_WIDTH,
        --! Address bus width
        ADDRESS_WIDTH  => ADDRESS_WIDTH,
        --! Block Ram Type, only 18Kb,36Kb blocks
        BRAM_TYPE      => BRAM_TYPE,
        --! Enable output register
        ENABLE_OUT_REG => ENABLE_OUT_REG,
        --! Select target device "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
        DEVICE         => DEVICE
    )
    port map (
        --! \name Interface A
        --! Clock A
        CLK     => clk,
        --! CLKA sync reset
        RST     => reset,
        --! Pipe enable
        PIPE_EN => pipe_en,
        --! Read Enable
        RE      => re,
        --! Write enable
        WE      => we,
        --! Address A
        ADDR    => addr,
        --! Data A In
        DI      => di,
        --! Data A Valid
        DO_DV   => do_dv,
        --! Data A Out
        DO      => do
    );

    -- Generate clock
    clk_gen_p : process
    begin
        clk <= '1';
        wait for CLKPER/2;
        clk <= '0';
        wait for CLKPER/2;
    end process;

    -- Generate reset
    reset_gen : process
    begin
        reset <= '1';
        wait for RESET_TIME;
        reset <= '0';
        wait;
    end process;

    --! Simulating input flow
    input_flow : process
    begin
        pipe_en <= '1';
        re      <= '0';
        we      <= '0';
        addr    <= (others => '0');
        di      <= (others => '0');

        wait for RESET_TIME;
        wait for CLKPER; wait until (clk'event and clk = '1');

        -- write on A, address -> 0
        di    <= (35 => '1', others => '0');
        we    <= '1';
        wait for CLKPER; wait until (clk'event and clk = '1');
        we    <= '0';
        wait for CLKPER; wait until (clk'event and clk = '1');

        -- read on A, address -> 0
        re    <= '1';
        addr  <= (0 => '0', others => '0');
        wait for CLKPER; wait until (clk'event and clk = '1');

        -- read on B, address -> 1
        re    <= '1';
        addr  <= (0 => '1', others => '0');
        wait for CLKPER; wait until (clk'event and clk = '1');
        re    <= '0';
        wait for CLKPER; wait until (clk'event and clk = '1');

        -- write on A, address -> X'802
        di    <= (36 => '1', others => '0');
        addr  <= (11 => '1', 1 => '1', others => '0');
        we    <= '1';
        wait for CLKPER; wait until (clk'event and clk = '1');

        -- read on A, address -> X'802
        we    <= '0';
        re    <= '1';
        addr  <= (11 => '1', 1 => '1', others => '0');
        wait for CLKPER; wait until (clk'event and clk = '1');
        re    <= '0';
        wait;
    end process;
end architecture;
