--! mux_dsp_gen.vhd
--!
--! \file
--! \author Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2015
--!
--! \section License
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

use work.math_pack.all;
use work.mux_lvl_func.all;

entity MUX_DSP_GEN_LOW is
    generic (
        DATA_WIDTH  : integer := 512;
        MUX_WIDTH   : integer := 8;
        --! Input pipeline registers (0, 1)
        REG_IN      : integer := 1;
        --! Output pipeline registers (0, 1)
        REG_OUT     : integer := 1;
        --! Pipeline between muxs levels (0, 1)
        REG_LVL     : integer := 1
    );
    port (
        --! Clock input
        CLK      : in  std_logic;
        --! Reset input
        RESET    : in  std_logic;
        --! Data input
        DATA_IN  : in  std_logic_vector(DATA_WIDTH*MUX_WIDTH-1 downto 0);
        --! Clock enable for input pipeline registers
        CE_IN    : in  std_logic;
        --! Clock enable for output pipeline registers
        CE_OUT   : in  std_logic;
        --! Clock enable for lvls
        CE_LVL   : in std_logic;
        --! Select input data
        SEL      : in std_logic_vector(log2(MUX_WIDTH)-1 downto 0);
        --! output
        DATA_OUT : out std_logic_vector(DATA_WIDTH-1 downto 0)
    );
end entity;

architecture FULL of MUX_DSP_GEN_LOW is
    constant NUM_LEVELS : integer := log2(MUX_WIDTH);

    type   array_inputs is array (0 to MUX_WIDTH) of std_logic_vector(DATA_WIDTH-1 downto 0);
    type   array_lvls is array (0 to NUM_LEVELS) of array_inputs;
    signal lvls_array       : array_lvls;
    signal lvls_array_cas   : array_lvls;
begin
    gen_inputs: for i in 0 to MUX_WIDTH-1 generate
        lvls_array(0)(I) <= DATA_IN(DATA_WIDTH-1+(I*DATA_WIDTH) downto (I*DATA_WIDTH));
    end generate;

    gen_levels: for lvl in 0 to NUM_LEVELS-1 generate
        constant NUM_OF_MUX  : integer := num_muxs(MUX_WIDTH, LVL);
        constant MOD_OF_MUX  : integer := mod_muxs(MUX_WIDTH, LVL);

        signal tmp_ce_in     : std_logic;
        signal tmp_ce_sel    : std_logic;
        signal tmp_ce_out    : std_logic;
    begin
        gen_first_in_true: if(LVL = 0) generate
            gen_ce: if(REG_IN = 1) generate
                tmp_ce_in      <= CE_IN;
                tmp_ce_sel     <= CE_IN;
            end generate;
            gen_ce_off: if(REG_IN = 0) generate
                tmp_ce_in      <= '1';
                tmp_ce_sel     <= '1';
            end generate;

        end generate;
        gen_first_in_false: if(LVL /= 0) generate
            gen_ce: if(REG_LVL = 1) generate
                tmp_ce_sel     <= CE_LVL;
            end generate;
            gen_ce_off: if(REG_LVL = 0) generate
                tmp_ce_sel     <= '1';
            end generate;

            tmp_ce_in      <= '1';
        end generate;

        gen_first_out_true: if(LVL = NUM_LEVELS-1) generate
            gen_ce: if(REG_OUT = 1) generate
                tmp_ce_out     <= CE_OUT;
            end generate;
            gen_ce_off: if(REG_OUT = 0) generate
                tmp_ce_out     <= '1';
            end generate;
            DATA_OUT <= lvls_array(LVL+1)(0);
        end generate;

        gen_first_out_false: if(LVL /= NUM_LEVELS-1) generate
            gen_ce: if(REG_LVL = 1) generate
                tmp_ce_out     <= CE_OUT;
            end generate;
            gen_ce_off: if(REG_LVL = 0) generate
                tmp_ce_out     <= '1';
            end generate;
        end generate;

        gen_muxs: for muxs in 0 to num_of_mux-1 generate
            constant PIPE_IN     : integer := gen_pipe_in(REG_IN, LVL);
            constant PIPE_SEL    : integer := gen_pipe_sel(REG_LVL, REG_IN, LVL);
            constant PIPE_OUT    : integer := gen_pipe_out(LVL, NUM_LEVELS-1, REG_OUT, REG_LVL);
            constant IN_CASCADE  : boolean := gen_in_cascade(LVL);

            signal tmp_a         : std_logic_vector(DATA_WIDTH-1 downto 0);
            signal tmp_b         : std_logic_vector(DATA_WIDTH-1 downto 0);
            signal tmp_sel       : std_logic_vector(0 downto 0);
        begin
            tmp_A <= lvls_array(LVL)(1+MUXS*2);
            gen_cas_off: if(in_cascade = false) generate
                tmp_B <= lvls_array(LVL)(MUXS*2);
            end generate;
            gen_cas_on: if(in_cascade = true) generate
                tmp_B <= lvls_array_cas(LVL)(MUXS*2);
            end generate;

            gne_pipe_sel: if(LVL > 0) generate
                sel_pipe_inst: entity work.PIPE_DSP
                generic map (
                    DATA_WIDTH => 1,
                    PIPE_EN    => true,
                    ENABLE_DSP => false,
                    NUM_REGS   => REG_IN + (LVL-1)
                )
                port map (
                    CLK      => CLK,
                    RESET    => RESET,
                    DATA_IN  => SEL(LVL downto LVL),
                    DATA_OUT => tmp_SEL,
                    CE       => CE_LVL
                );
            end generate;

            gne_pipe_no_sel: if(LVL = 0) generate
                tmp_SEL <= SEL(LVL downto LVL);
            end generate;

            mux_dsp_inst: entity work.MUX_DSP
            generic map (
                DATA_WIDTH     => DATA_WIDTH,
                REG_IN_A       => pipe_in,
                REG_IN_B       => pipe_in,
                REG_SEL        => pipe_sel,
                REG_OUT        => pipe_out,
                EN_CASCADE_IN  => in_cascade,
                NEG_SEL        => true
            )
            port map (
                CLK      => CLK,
                RESET    => RESET,
                A        => tmp_A,
                B        => tmp_B,
                CE_IN_A  => tmp_ce_in,
                CE_IN_B  => tmp_ce_in,
                CE_SEL   => tmp_ce_sel,
                SEL      => tmp_SEL(0),
                CE_OUT   => tmp_ce_out,
                P        => lvls_array(LVL+1)(MUXS),
                P_CAS    => lvls_array_cas(LVL+1)(MUXS)
            );
        end generate;

        gne_last: if (mod_of_mux > 0) generate
            signal tmp_pipe : std_logic_vector(DATA_WIDTH-1 downto 0);
        begin
            process (CLK)
            begin
                if ((CLK'event) and (CLK = '1')) then
                    if (RESET = '1') then
                        tmp_pipe <= (others => '0');
                    elsif (CE_OUT = '1') then
                        tmp_pipe <= lvls_array(LVL)(num_of_mux*2);
                    end if;
                end if;
            end process;

            lvls_array(LVL+1)(num_of_mux) <= tmp_pipe;
        end generate;
    end generate;
end architecture;
