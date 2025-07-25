-- clk_gen_tb.vhd: Clock generation entity testbench
-- Copyright (C) 2003 CESNET, Liberouter project
-- Author(s): Jan Korenek <korenek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- ----------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------

entity TESTBENCH is

end entity;

architecture BEHAVIORAL of TESTBENCH is

    constant ITEM : integer := 8;

    signal u1_addr   : std_logic_vector(2 downto 0);
    signal u1_do     : std_logic_vector(7 downto 0);
    signal u1_enable : std_logic;

    signal u2_addr   : std_logic_vector(2 downto 0);
    signal u2_di     : std_logic_vector(7 downto 0);
    signal u2_enable : std_logic;

begin


    -- ------------------- Clock generation component ----------------
    uut1 : entity work.DEC1FN_ENABLE
    generic map (

        ITEMS => item

    )

    port map (
        -- Input

        ADDR            => u1_addr,
        DO              => u1_do,
        ENABLE          => u1_enable

    );

    uut2 : entity work.DEC1FN2B
    generic map (

        ITEMS => item

    )

    port map (
        -- Input

        ADDR            => u2_addr,
        DI              => u2_di,
        ENABLE          => u2_enable

    );

    -- ----------------------------------------------------------------
    --                           Testbench Body
    -- ----------------------------------------------------------------

    u2_di <= u1_do;

    sim : process
    begin


        -- after start


        wait for 400 ns;


        --    u2_enable <= '1';
        --    wait for 20 ns;
        --
        --    u2_di <= "10000000";
        --    wait for 100 ns;
        --    u2_di <= "01000000";
        --    wait for 100 ns;
        --    u2_di <= "00100000";
        --    wait for 100 ns;
        --    u2_di <= "00010000";
        --    wait for 100 ns;
        --    u2_di <= "00001000";
        --    wait for 100 ns;
        --    u2_di <= "00000100";
        --    wait for 100 ns;
        --    u2_di <= "00000010";
        --    wait for 100 ns;
        --    u2_di <= "00000001";
        --    wait for 100 ns;
        --
        --    u2_enable <= '0';
        --    wait for 20 ns;
        --
        --    u2_di <= "10000000";
        --    wait for 100 ns;
        --    u2_di <= "01000000";
        --    wait for 100 ns;
        --    u2_di <= "00100000";
        --    wait for 100 ns;
        --    u2_di <= "00010000";
        --    wait for 100 ns;
        --    u2_di <= "00001000";
        --    wait for 100 ns;
        --    u2_di <= "00000100";
        --    wait for 100 ns;
        --    u2_di <= "00000010";
        --    wait for 100 ns;
        --    u2_di <= "00000001";
        --    wait for 100 ns;

        u1_enable <= '1';
        u2_enable <= '1';
        wait for 20 ns;

        u1_addr <= "000";
        wait for 100 ns;
        u1_addr <= "001";
        wait for 100 ns;
        u1_addr <= "010";
        wait for 100 ns;
        u1_addr <= "011";
        wait for 100 ns;
        u1_addr <= "100";
        wait for 100 ns;
        u1_addr <= "101";
        wait for 100 ns;
        u1_addr <= "110";
        wait for 100 ns;
        u1_addr <= "111";
        wait for 100 ns;

        u1_enable <= '0';
        wait for 20 ns;

        u1_addr <= "000";
        wait for 100 ns;
        u1_addr <= "001";
        wait for 100 ns;
        u1_addr <= "010";
        wait for 100 ns;
        u1_addr <= "011";
        wait for 100 ns;
        u1_addr <= "100";
        wait for 100 ns;
        u1_addr <= "101";
        wait for 100 ns;
        u1_addr <= "110";
        wait for 100 ns;
        u1_addr <= "111";
        wait for 100 ns;

        u1_enable <= '1';
        u2_enable <= '0';
        wait for 20 ns;

        u1_addr <= "000";
        wait for 100 ns;
        u1_addr <= "001";
        wait for 100 ns;
        u1_addr <= "010";
        wait for 100 ns;
        u1_addr <= "011";
        wait for 100 ns;
        u1_addr <= "100";
        wait for 100 ns;
        u1_addr <= "101";
        wait for 100 ns;
        u1_addr <= "110";
        wait for 100 ns;
        u1_addr <= "111";
        wait for 100 ns;

        u1_enable <= '0';
        wait for 20 ns;

        u1_addr <= "000";
        wait for 100 ns;
        u1_addr <= "001";
        wait for 100 ns;
        u1_addr <= "010";
        wait for 100 ns;
        u1_addr <= "011";
        wait for 100 ns;
        u1_addr <= "100";
        wait for 100 ns;
        u1_addr <= "101";
        wait for 100 ns;
        u1_addr <= "110";
        wait for 100 ns;
        u1_addr <= "111";
        wait for 100 ns;

        wait;

    end process;

end architecture;
