-- testbench.vhd: Testbench for simulation
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity TESTBENCH is
end entity;

architecture BEHAVIORAL Of TESTBENCH is
    constant DATA_WIDTH         : integer := 8;
    constant MAX_PARALEL_EVENTS : integer := 10;

    constant CLK_PERIOD         : time := 10 ns;

    signal sim_end              : std_logic := '0';
    signal clk                  : std_logic := '0';
    signal rst                  : std_logic := '0';

    signal start_event          : std_logic := '0';
    signal end_event            : std_logic := '0';
    signal latency_vld          : std_logic := '0';
    signal latency              : std_logic_vector(DATA_WIDTH - 1 downto 0);

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

    uut : entity work.LATENCY_METER
    generic map (
        DATA_WIDTH              => DATA_WIDTH,
        MAX_PARALEL_EVENTS      => MAX_PARALEL_EVENTS
    )
    port map (
        CLK                     => clk,
        RST                     => rst,
        START_EVENT             => start_event,
        END_EVENT               => end_event,
        LATENCY_VLD             => latency_vld,
        LATENCY                 => latency
    );


   -- Clock generation
    clk <= not clk after CLK_PERIOD / 2 when sim_end = '0' else '0';

    res_p : process
    begin
        wait until rising_edge(clk) and latency_vld = '1';
        echo("    latency = " & integer'image(to_integer(unsigned(latency))));
    end process;


    main_p : process is

        procedure req_p (delay : in integer; paraler : in boolean := false)
        is
        begin
            start_event <= transport '1';
            start_event <= transport '0' after (1 ps + CLK_PERIOD);
            end_event   <= transport '1' after (1 ps + CLK_PERIOD * delay);
            end_event   <= transport '0' after (1 ps + CLK_PERIOD * (delay + 1));

            echo("expecting " & integer'image(delay));

            if (paraler) then
                wait until rising_edge(clk);
            else
                wait until rising_edge(clk) and latency_vld = '1';
            end if;
        end procedure;

    begin
        sim_end     <= '0';
        start_event <= '0';
        end_event   <= '0';

        rst         <= '1';
        wait for CLK_PERIOD * 2;
        wait until rising_edge(clk);
        rst         <= '0';
        wait for CLK_PERIOD * 3;
        wait until rising_edge(clk);


        -- Try couner overflow
        wait for CLK_PERIOD * 200;
        wait until rising_edge(clk);


        req_p(4);
        req_p(100);
        req_p(200);
        req_p(1);
        req_p(0);
        req_p(200);

        req_p(50, true);
        req_p(51, true);
        req_p(70, true);

        wait for CLK_PERIOD * 200;
        wait until rising_edge(clk);

        req_p(3, true);
        wait until rising_edge(clk);
        wait until rising_edge(clk);
        req_p(3, true);
        wait until rising_edge(clk);


        wait for CLK_PERIOD * 10;
        wait until rising_edge(clk);

        for i in 0 to 10 loop
            req_p(4, true);
        end loop;

        wait for CLK_PERIOD * 10;
        wait until rising_edge(clk);

        for i in 0 to 10 loop
            req_p(i + 1, true);
        end loop;

        wait for CLK_PERIOD * 200;
        wait until rising_edge(clk);

        sim_end    <= '1';
        wait;
    end process;

end architecture;
