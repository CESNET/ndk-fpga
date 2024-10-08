-- testbench.vhd: Testbench for simulation of emif_referesh component
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

use work.hist_types.all;

entity TESTBENCH is
end entity;

architecture BEHAVIORAL Of TESTBENCH is
    constant DATA_WIDTH             : integer := 8;
    constant CNT_WIDTH              : integer := 8;
    constant CNTER_CNT              : integer := DATA_WIDTH;
    constant CLK_PERIOD             : time := 4 ns;

    signal clk                      : std_logic;
    signal rst                      : std_logic;
    signal sim_done                 : std_logic := '0';

    signal input_vld                : std_logic;
    signal input                    : std_logic_vector(DATA_WIDTH - 1 downto 0);
    signal sel_cnter                : std_logic_vector(log2(DATA_WIDTH) - 1 downto 0);
    signal output                   : std_logic_vector(CNT_WIDTH - 1 downto 0);
    signal cnt_ovf                  : std_logic;

begin

    ---------
    -- UUT --
    ---------

    uut : entity work.HISTOGRAMER
    generic map (
        VARIANT         => LINEAR, --LOG,
        DATA_WIDTH      => DATA_WIDTH,
        CNT_WIDTH       => CNT_WIDTH,
        CNTER_CNT       => CNTER_CNT
    )
    port map (
        CLK             => clk,
        RST             => rst,
        INPUT_VLD       => input_vld,
        INPUT           => input,
        SEL_CNTER       => sel_cnter,
        OUTPUT          => output,
        CNT_OVF         => cnt_ovf
    );

    -- clock generators
    clk_gen_p : process
    begin
        if (sim_done = '1') then
            wait;
        end if;

        clk <= '1';
        wait for CLK_PERIOD / 2;
        clk <= '0';
        wait for CLK_PERIOD / 2;
    end process;

    -- reset generators
    reset_gen_p : process
    begin
        if (sim_done = '1') then
            wait;
        end if;

        rst <= '1';
        wait for 2 * CLK_PERIOD;
        rst <= '0';
        wait;
    end process;

    main_p : process
    begin
        sim_done    <= '0';
        wait until rst = '0';


        input       <= "00000001";
        wait until rising_edge(clk);
        input_vld   <= '1';
        wait until rising_edge(clk);
        input_vld   <= '0';
        for i in 0 to CNTER_CNT - 1 loop
            sel_cnter <= std_logic_vector(to_unsigned(i, sel_cnter'length));
            wait for CLK_PERIOD;
        end loop;


        input       <= "00000010";
        wait until rising_edge(clk);
        input_vld   <= '1';
        wait until rising_edge(clk);
        input_vld   <= '0';
        for i in 0 to CNTER_CNT - 1 loop
            sel_cnter <= std_logic_vector(to_unsigned(i, sel_cnter'length));
            wait for CLK_PERIOD;
        end loop;


        input       <= "00100000";
        wait until rising_edge(clk);
        input_vld   <= '1';
        wait until rising_edge(clk);
        input_vld   <= '0';
        for i in 0 to CNTER_CNT - 1 loop
            sel_cnter <= std_logic_vector(to_unsigned(i, sel_cnter'length));
            wait for CLK_PERIOD;
        end loop;


        input       <= "11110000";
        wait until rising_edge(clk);
        input_vld   <= '1';
        wait until rising_edge(clk);
        input_vld   <= '0';
        for i in 0 to CNTER_CNT - 1 loop
            sel_cnter <= std_logic_vector(to_unsigned(i, sel_cnter'length));
            wait for CLK_PERIOD;
        end loop;


        input       <= "00011111";
        wait until rising_edge(clk);
        input_vld   <= '1';
        wait until rising_edge(clk);
        input_vld   <= '0';
        for i in 0 to CNTER_CNT - 1 loop
            sel_cnter <= std_logic_vector(to_unsigned(i, sel_cnter'length));
            wait for CLK_PERIOD;
        end loop;


        wait for CLK_PERIOD * 20;
        sim_done    <= '1';
        wait;
    end process;

end architecture;
