-- testbench.vhd: Testbench VHDL file
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity testbench is
end testbench;

architecture FULL of testbench is

    constant CLK_PERIOD : time := 5 ns;

    constant DATA_WIDTH         : natural := 8;
    constant ITEMS              : natural := 32;
    constant RD_PORTS           : natural := 1;
    constant RD_LATENCY         : natural := 1;
    constant WRITE_USE_RD_ADDR0 : boolean := false;
    constant DEVICE             : string  := "STRATIX10"; -- ULTRASCALE, STRATIX10

    signal clk     : std_logic;
    signal wr_en   : std_logic;
    signal wr_addr : std_logic_vector(log2(ITEMS)-1 downto 0);
    signal wr_data : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal rd_addr : std_logic_vector(RD_PORTS*log2(ITEMS)-1 downto 0);
    signal rd_data : std_logic_vector(RD_PORTS*DATA_WIDTH-1 downto 0);

begin

    clk_gen : process
    begin
        clk <= '1';
        wait for CLK_PERIOD / 2;
        clk <= '0';
        wait for CLK_PERIOD / 2;
    end process;

    -- =========================================================================
    --  DUT
    -- =========================================================================

    dut_i : entity work.GEN_LUTRAM
    generic map (
        DATA_WIDTH         => DATA_WIDTH,
        ITEMS              => ITEMS,
        RD_PORTS           => RD_PORTS,
        RD_LATENCY         => RD_LATENCY,
        WRITE_USE_RD_ADDR0 => WRITE_USE_RD_ADDR0,
        DEVICE             => DEVICE
    )
    port map (
        CLK     => clk,
        WR_EN   => wr_en,
        WR_ADDR => wr_addr,
        WR_DATA => wr_data,
        RD_ADDR => rd_addr,
        RD_DATA => rd_data
    );

    -- =========================================================================
    --  SIMULATION PROCESS
    -- =========================================================================

    sim_p : process
    begin

        wr_en <= '0';
        wr_addr <= (others => '0');
        wr_data <= (others => '0');
        rd_addr <= (others => '0');

        wait for 1.1 * CLK_PERIOD;

        for i in 0 to ITEMS-1 loop
            wr_en <= '1';
            wr_addr <= std_logic_vector(to_unsigned(i,log2(ITEMS)));
            wr_data <= std_logic_vector(to_unsigned(i,DATA_WIDTH));
            rd_addr <= std_logic_vector(to_unsigned(i,log2(ITEMS)));
            wait for CLK_PERIOD;
        end loop;

        for i in 0 to ITEMS-1 loop
            wr_en <= '0';
            rd_addr <= std_logic_vector(to_unsigned(i,log2(ITEMS)));
            wait for CLK_PERIOD;
        end loop;

        for i in 0 to ITEMS-1 loop
            wr_en <= '1';
            wr_addr <= std_logic_vector(to_unsigned(i,log2(ITEMS)));
            wr_data <= std_logic_vector(to_unsigned(32+i,DATA_WIDTH));
            rd_addr <= std_logic_vector(to_unsigned(i,log2(ITEMS)));
            wait for CLK_PERIOD;
        end loop;

        wr_en <= '0';

        for i in 0 to ITEMS-1 loop
            rd_addr <= std_logic_vector(to_unsigned(i,log2(ITEMS)));
            wait for CLK_PERIOD;
        end loop;

        wait;
    end process;

end FULL;
