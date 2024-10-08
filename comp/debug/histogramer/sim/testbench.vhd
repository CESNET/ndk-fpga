-- testbench.vhd: Testbench for simulation of mem_tester component
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.mi_sim_pkg.all;
use work.math_pack.all;
use work.type_pack.all;


entity TESTBENCH is
end entity;

architecture BEHAVIORAL Of TESTBENCH is

    constant INPUT_WIDTH            : integer := 16;
    constant BOX_WIDTH              : integer := 4;
    constant BOX_CNT                : integer := 32;
    constant READ_PRIOR             : boolean := false;

    constant BOX_SIZE               : integer := 2**INPUT_WIDTH / BOX_CNT;
    constant CLK_PERIOD             : time := 4 ns;     -- 266.66 MHz
    constant RST_TIME               : time := 40 ns;

    signal sim_done                 : std_logic := '0';

    signal clk                      : std_logic := '0';
    signal rst                      : std_logic;
    signal rst_done                 : std_logic;

    signal input_vld                : std_logic;
    signal input                    : std_logic_vector(INPUT_WIDTH - 1 downto 0);

    signal read_req                 : std_logic;
    signal read_addr                : std_logic_vector(log2(BOX_CNT) - 1 downto 0);
    signal read_box_vld             : std_logic;
    signal read_box                 : std_logic_vector(BOX_WIDTH - 1 downto 0);

    procedure echo (arg : in string := ""; endl : in boolean := true) is
    begin
        if (endl) then
            std.textio.write(std.textio.output, arg & LF);
        else
            std.textio.write(std.textio.output, arg);
        end if;
    end procedure echo;

begin

    ---------
    -- UUT --
    ---------

    uut : entity work.HISTOGRAMER
    generic map(
        INPUT_WIDTH             => INPUT_WIDTH,
        BOX_WIDTH               => BOX_WIDTH,
        BOX_CNT                 => BOX_CNT,
        READ_PRIOR              => READ_PRIOR
    )
    port map(
        CLK                     => clk,
        RST                     => rst,
        RST_DONE                => rst_done,

        INPUT                   => input,
        INPUT_VLD               => input_vld,

        READ_REQ                => read_req,
        READ_ADDR               => read_addr,
        READ_BOX_VLD            => read_box_vld,
        READ_BOX                => read_box
    );

    clk     <= not clk after CLK_PERIOD / 2 when sim_done /= '1' else '0';

    read_data_vld_p : process
    begin
        wait until rising_edge(clk) and read_box_vld = '1';
        echo("                      " & integer'image(to_integer(unsigned(read_box))));
    end process;

    test_p : process
        procedure input_p (val : in integer)
        is
        begin
            input       <= std_logic_vector(to_unsigned(val, INPUT_WIDTH));
            input_vld   <= '1';
            wait until rising_edge(clk);
            input_vld   <= '0';
            echo(integer'image(val));
        end procedure;

        procedure read_p (addr : in integer)
        is
        begin
            read_addr   <= std_logic_vector(to_unsigned(addr, log2(BOX_CNT)));
            read_req    <= '1';
            wait until rising_edge(clk);
            read_req    <= '0';
            echo("          " & integer'image(addr));
        end procedure;

        procedure read_all_p
        is
        begin
            wait until rising_edge(clk);
            wait until rising_edge(clk);

            for i in 0 to BOX_CNT - 1 loop
                read_p(i);
            end loop;
        end procedure;


    begin
        echo("");
        echo("");
        echo("");
        echo("Input     Read addr   Read box");
        sim_done            <= '0';

        rst                 <= '1';
        wait for RST_TIME;
        rst                 <= '0';
        wait until rst_done = '1';

        input_vld           <= '0';
        read_req            <= '0';
        wait for CLK_PERIOD * 10;
        wait until rising_edge(clk);

        -- Basic test
        for i in 0 to BOX_CNT - 1 loop
            input_p(i * BOX_SIZE);
        end loop;
        read_all_p;

        -- Test collisions
        for i in 0 to 10 - 1 loop
            input_p(0);
        end loop;
        read_all_p;

        for i in 0 to BOX_CNT - 1 loop
            if ((i + 1) mod 5 = 0) then
                input_p((i - 1) * BOX_SIZE);
            else
                input_p(i * BOX_SIZE);
            end if;
        end loop;
        read_all_p;

        -- Test box overflow
        for i in 0 to 2 ** BOX_WIDTH + 1 loop
            input_p(BOX_SIZE + 1);
        end loop;
        wait until rising_edge(clk);
        wait until rising_edge(clk);
        read_p(1);

        -- Test R/W collisions
        for i in 0 to BOX_CNT - 1 loop
            if ((i + 1) mod 5 = 0) then
                read_p(0);
            else
                input_p(0);
            end if;
        end loop;
        read_p(0);

        wait for CLK_PERIOD * 5;
        wait until rising_edge(clk);
        read_p(0);

        wait for CLK_PERIOD * 10;
        wait until rising_edge(clk);

        echo ("|| Simulation DONE ||");
        sim_done    <= '1';
        wait;

    end process;
end architecture;
