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
    constant MEM_DATA_WIDTH         : integer := 512;
    constant MEM_ADDR_WIDTH         : integer := 26;
    constant MEM_BURST_COUNT_WIDTH  : integer := 7;
    constant MEM_FREQ_KHZ           : integer := 266660;

    constant MI_DATA_WIDTH          : integer := 32;
    constant MI_ADDR_WIDTH          : integer := 32;


    constant CLK_PERIOD             : time := 4 ns;     -- 266.66 MHz
    constant RST_TIME               : time := 40 ns;

    signal sim_done                 : std_logic := '0';

    signal clk                      : std_logic := '0';
    signal rst                      : std_logic;
    signal rst_done                 : std_logic;

    signal mem_ready                : std_logic;
    signal mem_read                 : std_logic;
    signal mem_write                : std_logic;
    signal mem_address              : std_logic_vector(MEM_ADDR_WIDTH - 1 downto 0);
    signal mem_read_data            : std_logic_vector(MEM_DATA_WIDTH - 1 downto 0);
    signal mem_write_data           : std_logic_vector(MEM_DATA_WIDTH - 1 downto 0);
    signal mem_burst_count          : std_logic_vector(MEM_BURST_COUNT_WIDTH - 1 downto 0);
    signal mem_read_data_valid      : std_logic;

    signal mi_dwr                   : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal mi_addr                  : std_logic_vector(MI_ADDR_WIDTH - 1 downto 0);
    signal mi_be                    : std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0);
    signal mi_rd                    : std_logic;
    signal mi_wr                    : std_logic;
    signal mi_ardy                  : std_logic;
    signal mi_drd                   : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
    signal mi_drdy                  : std_logic;

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

    uut : entity work.MEM_LOGGER
    generic map (
        MEM_DATA_WIDTH          => MEM_DATA_WIDTH       ,
        MEM_ADDR_WIDTH          => MEM_ADDR_WIDTH       ,
        MEM_BURST_COUNT_WIDTH   => MEM_BURST_COUNT_WIDTH,
        MEM_FREQ_KHZ            => MEM_FREQ_KHZ         ,
        MI_DATA_WIDTH           => MI_DATA_WIDTH        ,
        MI_ADDR_WIDTH           => MI_ADDR_WIDTH
    )
    port map (
        CLK                     => clk                ,
        RST                     => rst                ,
        RST_DONE                => rst_done           ,
        MEM_READY               => mem_ready          ,
        MEM_READ                => mem_read           ,
        MEM_WRITE               => mem_write          ,
        MEM_ADDRESS             => mem_address        ,
        MEM_READ_DATA           => mem_read_data      ,
        MEM_WRITE_DATA          => mem_write_data     ,
        MEM_BURST_COUNT         => mem_burst_count    ,
        MEM_READ_DATA_VALID     => mem_read_data_valid,
        MI_DWR                  => mi_dwr             ,
        MI_ADDR                 => mi_addr            ,
        MI_BE                   => mi_be              ,
        MI_RD                   => mi_rd              ,
        MI_WR                   => mi_wr              ,
        MI_ARDY                 => mi_ardy            ,
        MI_DRD                  => mi_drd             ,
        MI_DRDY                 => mi_drdy
    );

    mi_sim_i : entity work.MI_SIM
    generic map (
        MI_SIM_ID                 => 0
    )
    port map (
        CLK                       => clk,
        RESET                     => rst,

        MI32_DWR                  => mi_dwr,
        MI32_ADDR                 => mi_addr,
        MI32_BE                   => mi_be,
        MI32_RD                   => mi_rd,
        MI32_WR                   => mi_wr,
        MI32_ARDY                 => mi_ardy,
        MI32_DRD                  => mi_drd,
        MI32_DRDY                 => mi_drdy
    );

    clk     <= not clk after CLK_PERIOD / 2 when sim_done /= '1' else '0';

    test_p : process
        variable addr : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
        variable data : std_logic_vector(MI_DATA_WIDTH - 1 downto 0);
        variable be   : std_logic_vector(MI_DATA_WIDTH / 8 - 1 downto 0)    := (others => '1');

        procedure read_p (addr_int : in integer)
        is
        begin
            addr := std_logic_vector(to_unsigned(addr_int, addr'length));
            work.mi_sim_pkg.ReadData(addr, data, be, status(0), 0);
            wait until rising_edge(clk);

            echo("Read " & integer'image(addr_int) & ": " & integer'image(to_integer(unsigned(data))));
        end procedure;

        procedure write_p (addr_int : in integer; val : in integer)
        is
        begin
            addr := std_logic_vector(to_unsigned(addr_int, addr'length));
            data := std_logic_vector(to_unsigned(val, data'length));
            be   := (others => '1');
            work.mi_sim_pkg.WriteData(addr, data, be, status(0), 0);
            wait until rising_edge(clk);

            --echo("Write: " & integer'image(val));
        end procedure;

        procedure stat_p (txt : in string; stat_id : in integer; index : in integer; slices : in integer := 1)
        is
        begin
            write_p(4, stat_id);
            write_p(8, index);
            echo(txt, false);
            echo(" (" & integer'image(index) & ") = ", false);

            for i in 0 to slices - 1 loop
                write_p(12, i);

                addr := std_logic_vector(to_unsigned(20, addr'length));
                work.mi_sim_pkg.ReadData(addr, data, be, status(0), 0);
                wait until rising_edge(clk);
                echo("  " & integer'image(to_integer(unsigned(data))), false);
            end loop;

            echo("");
        end procedure;

        procedure hist_p (index : in integer; boxes :in integer; slices : in integer := 1)
        is
        begin
            write_p(4, 17);
            write_p(8, index);
            echo("HIST (" & integer'image(index) & "):");

            for b in 0 to boxes - 1 loop
                write_p(16, b);

                for i in 0 to slices - 1 loop
                    write_p(12, i);

                    addr := std_logic_vector(to_unsigned(20, addr'length));
                    work.mi_sim_pkg.ReadData(addr, data, be, status(0), 0);
                    wait until rising_edge(clk);
                    echo("  " & integer'image(to_integer(unsigned(data))), false);
                end loop;
                echo("");
            end loop;

            echo("");
        end procedure;

    begin
        echo("");
        echo("");
        echo("");
        sim_done            <= '0';

        mem_ready           <= '0';
        mem_write           <= '0';
        mem_read            <= '0';
        mem_burst_count     <= (others => '0');
        mem_write_data      <= (others => '0');
        mem_read_data       <= (others => '0');
        mem_read_data_valid <= '0';

        rst                 <= '1';
        wait for RST_TIME;
        rst                 <= '0';
        wait until rising_edge(clk);
        wait until rst_done = '1';

        wait for CLK_PERIOD * 10;
        wait until rising_edge(clk);

        -- Single write
        mem_ready           <= '1';
        mem_write           <= '1';
        mem_read            <= '0';
        mem_burst_count     <= std_logic_vector(to_unsigned(1,   MEM_BURST_COUNT_WIDTH));
        mem_write_data      <= std_logic_vector(to_unsigned(777, MEM_DATA_WIDTH));
        mem_read_data       <= std_logic_vector(to_unsigned(0,   MEM_DATA_WIDTH));
        mem_read_data_valid <= '0';
        wait until rising_edge(clk);
        mem_write           <= '0';

        -- Write with interrupt
        mem_ready           <= '1';
        mem_write           <= '1';
        mem_burst_count     <= std_logic_vector(to_unsigned(3,   MEM_BURST_COUNT_WIDTH));
        wait until rising_edge(clk);
        mem_burst_count     <= std_logic_vector(to_unsigned(0,   MEM_BURST_COUNT_WIDTH));
        wait until rising_edge(clk);
        mem_ready           <= '0';
        wait until rising_edge(clk);
        mem_ready           <= '1';
        wait until rising_edge(clk);
        mem_write           <= '0';

        -- Read burst = 1
        mem_ready           <= '1';
        mem_read            <= '1';
        mem_burst_count     <= std_logic_vector(to_unsigned(1,   MEM_BURST_COUNT_WIDTH));
        wait until rising_edge(clk);
        wait until rising_edge(clk);
        wait until rising_edge(clk);
        mem_read            <= '0';
        wait for CLK_PERIOD * 10;
        wait until rising_edge(clk);
        mem_read_data       <= std_logic_vector(to_unsigned(777, MEM_DATA_WIDTH));
        mem_read_data_valid <= '1';
        wait until rising_edge(clk);
        wait until rising_edge(clk);
        mem_read_data_valid <= '0';
        wait until rising_edge(clk);
        mem_read_data_valid <= '1';
        wait until rising_edge(clk);
        mem_read_data_valid <= '0';
        wait until rising_edge(clk);

        -- Set latency to first words
        write_p(4, 11);
        write_p(12, 0);
        write_p(20, 1);

        -- Read burst = 7
        mem_ready           <= '1';
        mem_read            <= '1';
        mem_burst_count     <= std_logic_vector(to_unsigned(7,   MEM_BURST_COUNT_WIDTH));
        wait until rising_edge(clk);
        mem_read            <= '0';
        wait for CLK_PERIOD * 10;
        wait until rising_edge(clk);
        for i in 0 to 7 - 1 loop
            mem_read_data       <= std_logic_vector(to_unsigned(i,   MEM_DATA_WIDTH));
            mem_read_data_valid <= '1';

            if (i = 5) then
                wait until rising_edge(clk);
                mem_read_data_valid <= '0';
            end if;
            wait until rising_edge(clk);
        end loop;
        mem_read_data_valid <= '0';
        wait until rising_edge(clk);

        -- Zero burst
        mem_ready           <= '1';
        mem_write           <= '1';
        mem_burst_count     <= std_logic_vector(to_unsigned(0,   MEM_BURST_COUNT_WIDTH));
        wait until rising_edge(clk);
        mem_ready           <= '1';
        mem_write           <= '0';
        mem_read            <= '1';
        mem_burst_count     <= std_logic_vector(to_unsigned(0,   MEM_BURST_COUNT_WIDTH));
        wait until rising_edge(clk);
        mem_read            <= '0';

        -- Read + write
        mem_ready           <= '1';
        mem_write           <= '1';
        mem_read            <= '1';
        mem_burst_count     <= std_logic_vector(to_unsigned(1,   MEM_BURST_COUNT_WIDTH));
        wait until rising_edge(clk);
        mem_write           <= '0';
        mem_read            <= '0';



        wait for CLK_PERIOD * 10;
        wait until rising_edge(clk);



        stat_p("CNTER_CNT         ", 0, 0);
        stat_p("VALUE_CNT         ", 1, 0);
        stat_p("MI_DATA_WIDTH     ", 2, 0);
        stat_p("CTRLO_WIDTH       ", 3, 0);
        stat_p("CTRLI_WIDTH       ", 4, 0);
        stat_p("CNTER_WIDTH       ", 5, 0);

        echo("Cnters:");
        stat_p("  write ticks          ", 13, 0);
        stat_p("  read  ticks          ", 13, 1);
        stat_p("  total ticks          ", 13, 2);
        stat_p("  wr req cnt           ", 13, 3);
        stat_p("  wr req words         ", 13, 4);
        stat_p("  rd req cnt           ", 13, 5);
        stat_p("  rd req words         ", 13, 6);
        stat_p("  rd resp words        ", 13, 7);
        stat_p("  err zero burst       ", 13, 8);
        stat_p("  err simult r/w       ", 13, 9);
        stat_p("  rdy hold read ticks  ", 13, 10);
        stat_p("  rdy hold write ticks ", 13, 11);
        stat_p("  no rd/wr req ticks   ", 13, 12);
        stat_p("  wait ticks           ", 13, 13);

        echo("Values:");
        for i in 0 to 2 - 1 loop
            stat_p("  VALUE_WIDTH     ", 6, i);
            stat_p("  VALUE_ENS       ", 7, i);
            stat_p("  SUM_EXTRA_WIDTH ", 8, i);
            stat_p("  HIST_BOX_CNT    ", 9, i);
            stat_p("  HIST_BOX_WIDTH  ", 10, i);
            stat_p("  value min       ", 14, i);
            stat_p("  value max       ", 15, i);
            stat_p("  value sum       ", 16, i);
            stat_p("  value cnt       ", 13, i + 10);
            hist_p(i, 10);
            echo("");
        end loop;


        -- SW reset
        write_p(0, 1);
        wait until rising_edge(clk);
        read_p(0);
        write_p(0, 0);
        wait for CLK_PERIOD * 200;
        wait until rising_edge(clk);
        read_p(0);
        stat_p("  write ticks       ", 13, 0);
        stat_p("  value sum         ", 16, 0);

        -- Test basic registers
        write_p(4, 7);
        write_p(8, 7);
        write_p(12, 7);
        write_p(16, 7);



        echo("CTRL REG");
        read_p(0);

        echo("STATS REG");
        read_p(4);

        echo("INDEX REG");
        read_p(8);

        echo("SLICE REG");
        read_p(12);

        echo("HIST REG");
        read_p(16);

        echo("VALUE REG");
        read_p(20);

        echo("DEAD BEEF");
        read_p(24);

        stat_p("INVALID stat", 100, 100, 100);

        wait for CLK_PERIOD * 10;
        wait until rising_edge(clk);

        echo ("|| Simulation DONE ||");
        sim_done    <= '1';
        wait;

    end process;
end architecture;
