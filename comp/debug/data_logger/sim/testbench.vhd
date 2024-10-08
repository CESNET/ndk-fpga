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
    constant MI_DATA_WIDTH          : integer := 32;
    constant MI_ADDR_WIDTH          : integer := 32;

    constant CNTER_CNT              : integer := 3;
    constant VALUE_CNT              : integer := 3;

    constant CTRLO_WIDTH            : integer := 60;
    constant CTRLI_WIDTH            : integer := 4;
    constant CNTER_WIDTH            : integer := 4;
    constant VALUE_WIDTH            : i_array_t(max(VALUE_CNT - 1, 0) downto 0) := (8, 8, 64);

    constant HIST_EN                : b_array_t(max(VALUE_CNT - 1, 0) downto 0) := (others => true);
    constant SUM_EXTRA_WIDTH        : i_array_t(max(VALUE_CNT - 1, 0) downto 0) := (others => 16);
    constant HIST_BOX_CNT           : i_array_t(max(VALUE_CNT - 1, 0) downto 0) := (others => 16);
    constant HIST_BOX_WIDTH         : i_array_t(max(VALUE_CNT - 1, 0) downto 0) := (others => 8);

    constant CTRLO_DEFAULT          : std_logic_vector(max(CTRLO_WIDTH - 1, 0) downto 0) := (others => '1');



    function add_arr (arr_0 : i_array_t; arr_1 : i_array_t) return i_array_t is
        variable tmp  : i_array_t(arr_0'high downto arr_0'low) := arr_0;
    begin
        if (arr_0'length > 0) then
            for i in arr_0'low to arr_0'high loop
                tmp(i) := arr_0(i) + arr_1(i);
            end loop;
        end if;

        return tmp;
    end function;
    constant SUM_WIDTH          : i_array_t(max(VALUE_CNT - 1, 0) downto 0) := add_arr(VALUE_WIDTH, SUM_EXTRA_WIDTH);
    constant MAX_DATA_WIDTH     : integer :=
        max(CTRLI_WIDTH,
        max(CTRLO_WIDTH,
        max(CNTER_WIDTH,
        max(max(VALUE_WIDTH),
        max(max(SUM_WIDTH), max(HIST_BOX_WIDTH))
    ))));
    constant MI_SLICES          : integer := div_roundup(MAX_DATA_WIDTH, MI_DATA_WIDTH);


    constant CLK_PERIOD             : time := 4 ns;     -- 266.66 MHz
    constant RST_TIME               : time := 40 ns;

    signal sim_done                 : std_logic := '0';

    signal clk                      : std_logic := '0';
    signal rst                      : std_logic;
    signal rst_done                 : std_logic;


    signal ctrlo                    : std_logic_vector(max(CTRLO_WIDTH - 1, 0) downto 0) := (others => '0');
    signal ctrli                    : std_logic_vector(max(CTRLI_WIDTH - 1, 0) downto 0) := (others => '0');
    signal cnters_incr              : std_logic_vector(max(CNTER_CNT - 1, 0) downto 0) := (others => '0');
    signal values_vld               : std_logic_vector(max(VALUE_CNT - 1, 0) downto 0) := (others => '0');
    signal value_0                  : std_logic_vector(VALUE_WIDTH(0) - 1 downto 0) := (others => '0');
    signal value_1                  : std_logic_vector(VALUE_WIDTH(1) - 1 downto 0) := (others => '0');
    signal value_2                  : std_logic_vector(VALUE_WIDTH(2) - 1 downto 0) := (others => '0');

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

    uut : entity work.DATA_LOGGER
    generic map (
        MI_DATA_WIDTH       => MI_DATA_WIDTH  ,
        MI_ADDR_WIDTH       => MI_ADDR_WIDTH  ,
        CNTER_CNT           => CNTER_CNT      ,
        VALUE_CNT           => VALUE_CNT      ,
        CTRLO_WIDTH         => CTRLO_WIDTH    ,
        CTRLI_WIDTH         => CTRLI_WIDTH    ,
        CNTER_WIDTH         => CNTER_WIDTH    ,
        VALUE_WIDTH         => VALUE_WIDTH    ,
        HIST_EN             => HIST_EN        ,
        SUM_EXTRA_WIDTH     => SUM_EXTRA_WIDTH,
        HIST_BOX_CNT        => HIST_BOX_CNT   ,
        HIST_BOX_WIDTH      => HIST_BOX_WIDTH ,
        CTRLO_DEFAULT       => CTRLO_DEFAULT
    )
    port map (
        CLK                 => clk     ,
        RST                 => rst     ,
        RST_DONE            => rst_done,
        CTRLO               => ctrlo   ,
        CTRLI               => ctrli   ,
        CNTERS_INCR         => cnters_incr,
        VALUES_VLD          => values_vld,
        VALUES              => (
            value_2 &
            value_1 &
            value_0
        ),
        MI_DWR              => mi_dwr  ,
        MI_ADDR             => mi_addr ,
        MI_BE               => mi_be   ,
        MI_RD               => mi_rd   ,
        MI_WR               => mi_wr   ,
        MI_ARDY             => mi_ardy ,
        MI_DRD              => mi_drd  ,
        MI_DRDY             => mi_drdy
    );

    uut_test_no_interface : entity work.DATA_LOGGER
    generic map (
        MI_DATA_WIDTH       => MI_DATA_WIDTH  ,
        MI_ADDR_WIDTH       => MI_ADDR_WIDTH
    )
    port map (
        CLK                 => clk     ,
        RST                 => rst     ,

        MI_DWR              => (others => '0'),
        MI_ADDR             => (others => '0'),
        MI_BE               => (others => '0'),
        MI_RD               => '0',
        MI_WR               => '0'
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

        rst                 <= '1';
        wait for RST_TIME;
        rst                 <= '0';
        wait until rising_edge(clk);
        wait until rst_done = '1';

        wait for CLK_PERIOD * 10;
        wait until rising_edge(clk);



        -- Test cnters
        cnters_incr(0)       <= '1';
        cnters_incr(1)       <= '1';
        cnters_incr(2)       <= '1';
        wait until rising_edge(clk);
        cnters_incr(0)       <= '0';
        cnters_incr(1)       <= '0';
        cnters_incr(2)       <= '0';

        -- Test cnter ovf
        for i in 0 to 2 ** CNTER_WIDTH + 1 loop
            cnters_incr(0)       <= '1';
            wait until rising_edge(clk);
            cnters_incr(0)       <= '0';
        end loop;


        ctrli               <= std_ulogic_vector(to_unsigned(7, ctrli'length));

        value_0             <= std_logic_vector(to_unsigned(5, value_0'length));
        value_1             <= std_logic_vector(to_unsigned(6, value_1'length));
        value_2             <= std_logic_vector(to_unsigned(7, value_2'length));
        values_vld          <= (others => '1');
        wait until rising_edge(clk);
        values_vld          <= (others => '0');

        value_0             <= std_logic_vector(to_unsigned(1, value_0'length));
        value_1             <= std_logic_vector(to_unsigned(2, value_1'length));
        value_2             <= std_logic_vector(to_unsigned(3, value_2'length));
        values_vld          <= (others => '1');
        wait until rising_edge(clk);
        values_vld          <= (others => '0');

        value_1             <= std_logic_vector(to_unsigned(5, value_1'length));
        values_vld(1)       <= '1';
        wait until rising_edge(clk);
        values_vld(1)       <= '0';

        value_1             <= std_logic_vector(to_unsigned(255, value_1'length));
        values_vld(1)       <= '1';
        wait until rising_edge(clk);
        values_vld(1)       <= '0';

        -- Test CTRLO
        write_p(4, 11);
        write_p(12, 0);
        write_p(20, 42);




        stat_p("CNTER_CNT         ", 0, 0);
        stat_p("VALUE_CNT         ", 1, 0);
        stat_p("MI_DATA_WIDTH     ", 2, 0);
        stat_p("CTRLO_WIDTH       ", 3, 0);
        stat_p("CTRLI_WIDTH       ", 4, 0);
        stat_p("CNTER_WIDTH       ", 5, 0);

        stat_p("ctrlo             ", 11, 0);
        stat_p("ctrli             ", 12, 0);

        echo("Cnters:");
        for i in 0 to CNTER_CNT - 1 loop
            stat_p("  cnter           ", 13, i);
        end loop;

        echo("Values:");
        for i in 0 to VALUE_CNT - 1 loop
            stat_p("  VALUE_WIDTH     ", 6, i);
            stat_p("  VALUE_ENS       ", 7, i);
            stat_p("  SUM_EXTRA_WIDTH ", 8, i);
            stat_p("  HIST_BOX_CNT    ", 9, i);
            stat_p("  HIST_BOX_WIDTH  ", 10, i);
            stat_p("  value min       ", 14, i);
            stat_p("  value max       ", 15, i);
            stat_p("  value sum       ", 16, i);
            stat_p("  value cnt       ", 13, i + CNTER_CNT);
            hist_p(i, 16);
            echo("");
        end loop;

        wait for CLK_PERIOD * 10;
        wait until rising_edge(clk);

        -- SW reset
        write_p(0, 1);
        wait until rising_edge(clk);
        read_p(0);
        write_p(0, 0);
        wait for CLK_PERIOD * 100;
        wait until rising_edge(clk);
        read_p(0);

        echo ("|| Simulation DONE ||");
        sim_done    <= '1';
        wait;

    end process;
end architecture;
