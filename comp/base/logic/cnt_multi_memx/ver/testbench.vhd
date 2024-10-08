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

entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of testbench is

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
    signal CLK                                : std_logic;
    signal RESET                              : std_logic;

    signal INC_CH       : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal INC_VAL      : std_logic_vector(INC_WIDTH-1 downto 0);
    signal INC_VLD      : std_logic;
    signal INC_RDY      : std_logic;
    signal RST_CH       : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal RST_VLD      : std_logic;
    signal RD_CH        : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal RD_VLD       : std_logic;
    signal RD_VAL       : std_logic_vector(CNT_WIDTH-1 downto 0); -- 1 CLK latency

    shared variable seed0 : positive := 42;
    shared variable seed1 : positive := 211;
    shared variable X     : integer;
    shared variable CH    : std_logic_vector(log2(CHANNELS)-1 downto 0);
    shared variable VAL   : std_logic_vector(INC_WIDTH-1 downto 0);

    shared variable go : boolean := false;
    signal final_ch : unsigned(1+log2(CHANNELS)-1 downto 0);

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
    generic map(
        DEVICE        => DEVICE       ,
        CHANNELS      => CHANNELS     ,
        CNT_WIDTH     => CNT_WIDTH    ,
        INC_WIDTH     => INC_WIDTH    ,
        INC_FIFO_SIZE => INC_FIFO_SIZE
    )
    port map(
        CLK     => CLK    ,
        RESET   => RESET  ,

        INC_CH  => INC_CH ,
        INC_VAL => INC_VAL,
        INC_VLD => INC_VLD,
        INC_RDY => INC_RDY,

        RST_CH  => RST_CH ,
        RST_VLD => RST_VLD,

        RD_CH   => RD_CH  ,
        RD_VLD  => RD_VLD ,
        RD_VAL  => RD_VAL
    );

    -- -------------------------------------------------------------------------
    --                        clk and reset generators
    -- -------------------------------------------------------------------------

    -- generating clk
    clk_gen: process
    begin
        for i in 0 to VER_LENGTH-1 loop
            go := true;
            CLK <= '1';
            wait for C_CLK_PER / 2;
            CLK <= '0';
            wait for C_CLK_PER / 2;
        end loop;
        go := false;
        for i in 0 to 100+4*CHANNELS-1 loop
            CLK <= '1';
            wait for C_CLK_PER / 2;
            CLK <= '0';
            wait for C_CLK_PER / 2;
        end loop;
        assert (cntr=cntr_ref) report "ERROR: Incorrect counter value!" severity failure;
        report "Verification finished successfully!";
        stop;
        wait;
    end process clk_gen;

    -- generating reset
    rst_gen: process
    begin
        RESET <= '1';
        wait for C_RST_TIME;
        RESET <= '0';
        wait;
    end process rst_gen;

    -- -------------------------------------------------------------------------

    gen_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            random_vector_proc(seed0,seed1,VAL);
            if ((or VAL)='0') then
                VAL := (0 => '1', others => '0');
            end if;
            INC_VAL <= VAL;

            random_vector_proc(seed0,seed1,CH);
            INC_CH <= CH;
            random_vector_proc(seed0,seed1,CH);
            RST_CH <= CH;
            --random_vector_proc(seed0,seed1,CH );
            RD_CH  <= CH;

            INC_VLD <= '0';
            RST_VLD <= '0';
            RD_VLD  <= '0';

            randint(seed0,seed1,0,99,X);
            if (X<INC_CHANCE) then
                INC_VLD <= '1';
            end if;
            randint(seed0,seed1,0,99,X);
            if (X<RST_CHANCE) then
                RST_VLD <= '1';
                RD_VLD  <= '1';
            end if;
            randint(seed0,seed1,0,99,X);
            if (X<RD_CHANCE) then
                RD_VLD  <= '1';
            end if;

            rst_vld_reg <= RST_VLD;
            rst_ch_reg  <= RST_CH;

            final_ch <= (others => '0');

            if (not go) then
                INC_VLD <= '0';
                RST_VLD <= final_ch(final_ch'high);
                RD_VLD  <= final_ch(final_ch'high);
                RST_CH  <= std_logic_vector(enlarge_left(final_ch,-1));
                RD_CH   <= std_logic_vector(enlarge_left(final_ch,-1));
                final_ch <= final_ch+1;
            end if;
        end if;
    end process;

    cntr_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            if (INC_VLD='1' and INC_RDY='1') then
                cntr_ref(to_integer(unsigned(INC_CH))) <= cntr_ref(to_integer(unsigned(INC_CH)))+unsigned(INC_VAL);
            end if;

            if (rst_vld_reg='1') then
                cntr(to_integer(unsigned(rst_ch_reg))) <= cntr(to_integer(unsigned(rst_ch_reg)))+unsigned(RD_VAL);
            end if;

            if (RESET='1') then
                cntr     <= (others => (others => '0'));
                cntr_ref <= (others => (others => '0'));
            end if;
        end if;
    end process;

end architecture behavioral;
