-- testbench.vhd: Testbench
-- Copyright (C) 2018 CESNET
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;

use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.math_real.all;
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity TESTBENCH is
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture BEHAVIORAL of TESTBENCH is

    -- Constants declaration ---------------------------------------------------
    -- Synchronization
    constant C_CLK_PER    : time := 5.0 ns;
    constant C_RST_TIME   : time := 10 * C_CLK_PER + 1 ns;

    constant S_DATA_WIDTH           : integer := 8;
    constant S_ITEMS                : integer := 6;
    constant S_LATENCY              : integer := 2;

    constant S_NONZERO_LAT : integer := max(1,S_LATENCY);

    -- Synchronization
    signal clk                                : std_logic;
    signal reset                              : std_logic;

    -- uut I/O
    signal s_in_data     : std_logic_vector(S_ITEMS*S_DATA_WIDTH-1 downto 0);
    signal s_in_data_arr : slv_array_t(S_ITEMS-1 downto 0)(S_DATA_WIDTH-1 downto 0);
    signal s_in_vld      : std_logic_vector(S_ITEMS-1 downto 0) := (others => '0');
    signal s_out_data    : std_logic_vector(S_DATA_WIDTH-1 downto 0);

    -- test signals
    signal s_fake_add_regs : slv_array_t(S_NONZERO_LAT-1 downto 0)(S_DATA_WIDTH-1 downto 0) := (others => (others => '0'));

    -- ----------------------------------------------------------------------------
    --                            Architecture body
    -- ----------------------------------------------------------------------------
begin

    -- -------------------------------------------------------------------------
    -- UUT
    -- -------------------------------------------------------------------------

    uut: entity work.PIPE_TREE_ADDER
    generic map (
        DATA_WIDTH => s_DATA_WIDTH,
        ITEMS      => s_ITEMS,
        LATENCY    => s_LATENCY
    )
    port map (
        CLK   => clk,
        RESET => reset,

        IN_DATA  => s_in_data,
        IN_VLD   => s_in_vld,
        OUT_DATA => s_out_data
    );

    -- -------------------------------------------------------------------------
    --                        clk and reset generators
    -- -------------------------------------------------------------------------

    -- generating clk
    clk_gen : process
    begin
        clk <= '1';
        wait for C_CLK_PER / 2;
        clk <= '0';
        wait for C_CLK_PER / 2;
    end process;

    -- generating reset
    rst_gen : process
    begin
        reset <= '1';
        wait for C_RST_TIME;
        reset <= '0';
        wait;
    end process;

    -- -------------------------------------------------------------------------
    -- test process
    -- -------------------------------------------------------------------------

    test : process
        variable seed1 : positive := S_ITEMS;
        variable seed2 : positive := S_LATENCY+1;

        variable rand : real;
        variable x    : integer;

        variable vld_ch : integer := 80; -- %

        variable e : integer := 0;

        variable data : unsigned(S_DATA_WIDTH-1 downto 0);
        variable sum  : unsigned(S_DATA_WIDTH-1 downto 0);
    begin
        wait for C_CLK_PER/2;
        if (reset = '1') then
            wait until reset = '0';
        end if;

        assert (e = 0)
            severity failure;

        if (S_LATENCY /= 0) then
            if (s_fake_add_regs(0) /= s_out_data) then
                report "Incorrect adding result!"
                    severity error;
                e := 1;
            end if;
        end if;

        for i in 0 to S_LATENCY-1-1 loop
            s_fake_add_regs(i) <= s_fake_add_regs(i+1);
        end loop;

        sum := (others => '0');

        for i in 0 to S_ITEMS-1 loop
            uniform(seed1,seed2,rand);
            data := to_unsigned(integer(rand*real(2**S_DATA_WIDTH)),S_DATA_WIDTH);

            s_in_vld(i)                                           <= '0';
            s_in_data(s_DATA_WIDTH*(i+1)-1 downto s_DATA_WIDTH*i) <= std_logic_vector(data);
            s_in_data_arr(i)                                      <= std_logic_vector(data);

            uniform(seed1,seed2,rand);
            x := integer(rand*100.0);
            if (x < vld_ch) then
                sum         := sum + data;
                s_in_vld(i) <= '1';
            end if;
        end loop;

        s_fake_add_regs(s_NONZERO_LAT-1) <= std_logic_vector(sum);

        wait for C_CLK_PER/2;

        if (S_LATENCY = 0) then
            if (std_logic_vector(sum) /= s_out_data) then
                report "Incorrect adding result!"
                    severity error;
                e := 1;
            end if;
        end if;

    end process;

end architecture;
