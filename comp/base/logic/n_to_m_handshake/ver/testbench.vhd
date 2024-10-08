-- testbench.vhd: Testbench for merger from n inputs to m outputs
-- Copyright (C) 2018 CESNET
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;

use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use IEEE.math_real.all;
use work.type_pack.all;
use work.math_pack.all;
use work.dma_bus_pack.all;
use work.basics_test_pkg.all;
use std.env.stop;
use STD.textio.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of testbench is

    -- Constants declaration ---------------------------------------------------

    -- Synchronization
    constant C_CLK_PER          : time := 5.0 ns;
    constant C_RST_TIME         : time := 10 * C_CLK_PER + 1 ns;

    constant TEST_TIME          : integer := 1000;

    constant SOURCES            : integer := 5;
    constant MAX_DATA_WIDTH     : integer := 8;
    constant DESTINATIONS       : integer := 4;
    constant OUTPUT_REG_EN      : boolean := true;

    constant ALL_RDY_CHANCE     : integer := 40; -- [%]

    -- Signals declaration -----------------------------------------------------

    -- Synchronization
    signal clk                                : std_logic;
    signal rst                                : std_logic;

    signal in_data     : slv_array_2d_t(SOURCES-1 downto 0)(DESTINATIONS-1 downto 0)(MAX_DATA_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal in_src_rdy  : std_logic_vector(SOURCES-1 downto 0);
    signal in_dst_rdy  : std_logic_vector(SOURCES-1 downto 0);

    signal out_data    : slv_array_2d_t(DESTINATIONS-1 downto 0)(SOURCES-1 downto 0)(MAX_DATA_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal out_src_rdy : std_logic_vector(DESTINATIONS-1 downto 0);
    signal out_dst_rdy : std_logic_vector(DESTINATIONS-1 downto 0);

    signal all_rdy     : std_logic;

    signal test_out_data     : slv_array_2d_t(DESTINATIONS-1 downto 0)(SOURCES-1 downto 0)(MAX_DATA_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal test_out_data_reg : slv_array_2d_t(DESTINATIONS-1 downto 0)(SOURCES-1 downto 0)(MAX_DATA_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    signal test_ok : std_logic := '1';

-- ----------------------------------------------------------------------------
--                            Architecture body
-- ----------------------------------------------------------------------------

begin

    -- -------------------------------------------------------------------------
    -- Unit under test
    -- -------------------------------------------------------------------------

    uut : entity work.N_TO_M_HANDSHAKE
    generic map(
        SOURCES        => SOURCES       ,
        MAX_DATA_WIDTH => MAX_DATA_WIDTH,
        DESTINATIONS   => DESTINATIONS  ,
        OUTPUT_REG_EN  => OUTPUT_REG_EN
    )
    port map(
        CLK         => clk,
        RESET       => rst,

        IN_DATA     => IN_DATA     ,
        IN_SRC_RDY  => IN_SRC_RDY  ,
        IN_DST_RDY  => IN_DST_RDY  ,

        OUT_DATA    => OUT_DATA    ,
        OUT_SRC_RDY => OUT_SRC_RDY ,
        OUT_DST_RDY => OUT_DST_RDY ,

        ALL_RDY     => ALL_RDY

    );

    -- -------------------------------------------------------------------------
    --                        clk and reset generators
    -- -------------------------------------------------------------------------

    -- generating clk
    clk_gen: process
    begin
        clk <= '1';
        wait for C_CLK_PER / 2;
        clk <= '0';
        wait for C_CLK_PER / 2;
    end process clk_gen;

    -- generating reset
    rst_gen: process
    begin
        rst <= '1';
        wait for C_RST_TIME;
        rst <= '0';
        wait;
    end process rst_gen;

    -- -------------------------------------------------------------------------

    tb : process
        variable seed1 : positive := 42;
        variable seed2 : positive := 42;

        variable rand  : real;
        variable X     : integer;
    begin
        wait for 1 ns;
        -- Wait for the reset
        if (rst='1') then
            wait until rst='0';
        end if;

        -- input gen
        for i in 0 to SOURCES-1 loop
            for e in 0 to DESTINATIONS-1 loop
                in_data(i)(e) <= random_vector(MAX_DATA_WIDTH,seed1);
                seed1 := seed1+1;
            end loop;
        end loop;
        in_src_rdy  <= random_vector(SOURCES,seed1);
        out_dst_rdy <= random_vector(DESTINATIONS,seed2);

        randint(seed1,seed2,0,99,X);
        if (X<ALL_RDY_CHANCE) then
            in_src_rdy  <= (others => '1');
            out_dst_rdy <= (others => '1');
        end if;

        wait for C_CLK_PER -1 ns;
    end process;

    -- input monitor
    input_monitor_pr : process (all)
    begin
        test_out_data <= (others => (others => (others => 'X')));
        for i in 0 to SOURCES-1 loop
            if (in_src_rdy(i)='1' and in_dst_rdy(i)='1') then
                for e in 0 to DESTINATIONS-1 loop
                    test_out_data(e)(i) <= in_data(i)(e);
                end loop;
            end if;
        end loop;
    end process;

    reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then
            for i in 0 to SOURCES-1 loop
                if (in_dst_rdy(i)='1') then
                    for e in 0 to DESTINATIONS-1 loop
                        test_out_data_reg(e)(i) <= test_out_data(e)(i);
                    end loop;
                end if;
            end loop;
        end if;
    end process;

    -- output monitor
    output_monitor_pr : process (CLK)
        variable v_test_out_data : slv_array_2d_t(DESTINATIONS-1 downto 0)(SOURCES-1 downto 0)(MAX_DATA_WIDTH-1 downto 0) := (others => (others => (others => '0')));
    begin
        if (rising_edge(CLK)) then
            test_ok <= '1';
            v_test_out_data := test_out_data;
            if (OUTPUT_REG_EN) then
                v_test_out_data := test_out_data_reg;
            end if;
            for i in 0 to DESTINATIONS-1 loop
                if (out_src_rdy(i)='1' and out_dst_rdy(i)='1') then
                    for e in 0 to SOURCES-1 loop
                        if (v_test_out_data(i)(e)/=out_data(i)(e)) then
                            test_ok <= '0';
                        end if;
                    end loop;
                end if;
            end loop;
        end if;
    end process;

    -- test run control
    time_pr : process
    begin
        for i in 0 to TEST_TIME-1 loop
            wait for C_CLK_PER;
            if (test_ok='0') then
                report "ERROR" severity failure;
                stop(1);
            end if;
        end loop;
        report "SUCCESS";
        stop(0);
    end process;

end architecture behavioral;
