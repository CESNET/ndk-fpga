-- testbench.vhd: Testbench for merger from n inputs to m outputs
-- Copyright (C) 2020 CESNET
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;

use IEEE.std_logic_1164.all;
use ieee.math_real.all;
use work.math_pack.all;
use ieee.numeric_std.all;
use work.type_pack.all;
use work.basics_test_pkg.all;
use std.env.stop;

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
    constant C_CLK_PER            : time := 5.0 ns;
    constant C_RST_TIME           : time := 10 * C_CLK_PER + 1 ns;
    constant VER_LENGTH           : natural := 100000;

    constant DEVICE               : string  := "ULTRASCALE";
    constant CHANNELS             : natural := 64;
    constant CNT_WIDTH            : natural := 32;
    constant INC_WIDTH            : natural := 8;
    constant INC_FIFO_SIZE        : natural := 64;

    constant INC_CHANCE : natural := 60;
    constant RST_CHANCE : natural := 50;
    constant RD_CHANCE  : natural := 40;

    -- Signals declaration -----------------------------------------------------

    -- Synchronization
    signal clk                                : std_logic;
    signal reset                              : std_logic;

    signal inc_ch       : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal inc_val      : std_logic_vector(INC_WIDTH-1 downto 0);
    signal inc_vld      : std_logic;
    signal inc_rdy      : std_logic;
    signal rst_ch       : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal rst_vld      : std_logic;
    signal rd_ch        : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal rd_vld       : std_logic;
    signal rd_val       : std_logic_vector(CNT_WIDTH-1 downto 0); -- 1 CLK latency

    shared variable seed0 : positive := 42;
    shared variable seed1 : positive := 211;
    shared variable x     : integer;
    shared variable ch    : std_logic_vector(log2(CHANNELS)-1 downto 0);
    shared variable val   : std_logic_vector(INC_WIDTH-1 downto 0);

    shared variable go       : boolean := false;
    signal          final_ch : unsigned(1+log2(CHANNELS)-1 downto 0);

    signal rst_vld_reg  : std_logic;
    signal rst_ch_reg   : std_logic_vector(log2(CHANNELS)-1 downto 0);

    signal cntr     : u_array_t(CHANNELS-1 downto 0)(CNT_WIDTH-1 downto 0);
    signal cntr_ref : u_array_t(CHANNELS-1 downto 0)(CNT_WIDTH-1 downto 0);

    -- ----------------------------------------------------------------------------
    --                            Architecture body
    -- ----------------------------------------------------------------------------

begin

    -- -------------------------------------------------------------------------
    -- CROSSBAR SCHEDULER planner
    -- -------------------------------------------------------------------------

    uut: entity work.CNT_MULTI_MEMX
    generic map (
        DEVICE        => DEVICE,
        CHANNELS      => CHANNELS,
        CNT_WIDTH     => CNT_WIDTH,
        INC_WIDTH     => INC_WIDTH,
        INC_FIFO_SIZE => INC_FIFO_SIZE
    )
    port map (
        CLK     => clk,
        RESET   => reset,

        INC_CH  => inc_ch,
        INC_VAL => inc_val,
        INC_VLD => inc_vld,
        INC_RDY => inc_rdy,

        RST_CH  => rst_ch,
        RST_VLD => rst_vld,

        RD_CH   => rd_ch,
        RD_VLD  => rd_vld,
        RD_VAL  => rd_val
    );

    -- -------------------------------------------------------------------------
    --                        clk and reset generators
    -- -------------------------------------------------------------------------

    -- generating clk
    clk_gen : process
    begin
        for i in 0 to VER_LENGTH-1 loop
            go  := true;
            clk <= '1';
            wait for C_CLK_PER / 2;
            clk <= '0';
            wait for C_CLK_PER / 2;
        end loop;
        go := false;
        for i in 0 to 100+4*CHANNELS-1 loop
            clk <= '1';
            wait for C_CLK_PER / 2;
            clk <= '0';
            wait for C_CLK_PER / 2;
        end loop;
        assert (cntr = cntr_ref)
            report "ERROR: Incorrect counter value!"
            severity failure;
        report "Verification finished successfully!";
        stop;
        wait;
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

    gen_pr : process (clk)
    begin
        if (rising_edge(clk)) then

            random_vector_proc(seed0,seed1,val);
            if ((or val) = '0') then
                val := (0 => '1', others => '0');
            end if;
            inc_val <= val;

            random_vector_proc(seed0,seed1,ch);
            inc_ch <= ch;
            random_vector_proc(seed0,seed1,ch);
            rst_ch <= ch;
            -- random_vector_proc(seed0,seed1,CH );
            rd_ch  <= ch;

            inc_vld <= '0';
            rst_vld <= '0';
            rd_vld  <= '0';

            randint(seed0,seed1,0,99,x);
            if (x < INC_CHANCE) then
                inc_vld <= '1';
            end if;
            randint(seed0,seed1,0,99,x);
            if (x < RST_CHANCE) then
                rst_vld <= '1';
                rd_vld  <= '1';
            end if;
            randint(seed0,seed1,0,99,x);
            if (x < RD_CHANCE) then
                rd_vld  <= '1';
            end if;

            rst_vld_reg <= rst_vld;
            rst_ch_reg  <= rst_ch;

            final_ch <= (others => '0');

            if (not go) then
                inc_vld  <= '0';
                rst_vld  <= final_ch(final_ch'high);
                rd_vld   <= final_ch(final_ch'high);
                rst_ch   <= std_logic_vector(enlarge_left(final_ch,-1));
                rd_ch    <= std_logic_vector(enlarge_left(final_ch,-1));
                final_ch <= final_ch+1;
            end if;
        end if;
    end process;

    cntr_pr : process (clk)
    begin
        if (rising_edge(clk)) then

            if (inc_vld = '1' and inc_rdy = '1') then
                cntr_ref(to_integer(unsigned(inc_ch))) <= cntr_ref(to_integer(unsigned(inc_ch)))+unsigned(inc_val);
            end if;

            if (rst_vld_reg = '1') then
                cntr(to_integer(unsigned(rst_ch_reg))) <= cntr(to_integer(unsigned(rst_ch_reg)))+unsigned(rd_val);
            end if;

            if (reset = '1') then
                cntr     <= (others => (others => '0'));
                cntr_ref <= (others => (others => '0'));
            end if;
        end if;
    end process;

end architecture;
