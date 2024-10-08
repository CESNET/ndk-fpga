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

    constant DATA_WIDTH         : natural := 4;
    constant ITEMS              : natural := 32;
    constant WR_PORTS           : natural := 2;
    constant RD_PORTS           : natural := 2;
    constant RD_LATENCY         : natural := 1;

    signal clk     : std_logic;
    signal wr_en   : std_logic_vector(WR_PORTS-1 downto 0);
    signal wr_addr : std_logic_vector(WR_PORTS*log2(ITEMS)-1 downto 0);
    signal wr_data : std_logic_vector(WR_PORTS*DATA_WIDTH-1 downto 0);
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

    dut_i : entity work.GEN_REG_ARRAY
    generic map (
        DATA_WIDTH         => DATA_WIDTH,
        ITEMS              => ITEMS,
        WR_PORTS           => WR_PORTS,
        RD_PORTS           => RD_PORTS,
        RD_LATENCY         => RD_LATENCY
    )
    port map (
        CLK     => clk,
        RESET   => '0',
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

        wr_en   <= (others => '0');
        wr_addr <= (others => '0');
        wr_data <= (others => '0');
        rd_addr <= (others => '0');

        wait for 1.1 * CLK_PERIOD;

        for w in 0 to WR_PORTS-1 loop
            for i in 0 to ITEMS-1 loop
                wr_en(w) <= '1';
                wr_addr((w+1)*log2(ITEMS)-1 downto w*log2(ITEMS)) <= std_logic_vector(to_unsigned(i,log2(ITEMS)));
                wr_data((w+1)*DATA_WIDTH-1 downto w*DATA_WIDTH) <= std_logic_vector(to_unsigned(w+1,DATA_WIDTH));
                rd_addr((w+1)*log2(ITEMS)-1 downto w*log2(ITEMS)) <= std_logic_vector(to_unsigned(i,log2(ITEMS)));
                wait for CLK_PERIOD;
            end loop;
            wr_en   <= (others => '0');
        end loop;

        -- write colision
        for w in 0 to WR_PORTS-1 loop
            wr_en(w) <= '1';
            wr_data((w+1)*DATA_WIDTH-1 downto w*DATA_WIDTH) <= std_logic_vector(to_unsigned(4-w,DATA_WIDTH));
            wait for CLK_PERIOD;
        end loop;

        wr_en   <= (others => '0');
        wr_addr <= (others => '0');
        wr_data <= (others => '0');
        rd_addr <= (others => '0');
        wait for CLK_PERIOD;

        for w in 0 to WR_PORTS-1 loop
            for i in 0 to ITEMS-1 loop
                rd_addr((w+1)*log2(ITEMS)-1 downto w*log2(ITEMS)) <= std_logic_vector(to_unsigned(i,log2(ITEMS)));
                wait for CLK_PERIOD;
            end loop;
        end loop;

        wait;
    end process;

end FULL;
