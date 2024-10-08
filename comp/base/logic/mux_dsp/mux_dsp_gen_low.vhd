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

architecture full of MUX_DSP_GEN_LOW is
   constant num_levels : integer := log2(MUX_WIDTH);

   type array_inputs is array (0 to MUX_WIDTH) of std_logic_vector(DATA_WIDTH-1 downto 0);
   type array_lvls is array (0 to num_levels) of array_inputs;
   signal lvls_array       : array_lvls;
   signal lvls_array_cas   : array_lvls;
begin
   GEN_INPUTS: for I in 0 to MUX_WIDTH-1 generate
      lvls_array(0)(I) <= DATA_IN(DATA_WIDTH-1+(I*DATA_WIDTH) downto (I*DATA_WIDTH));
   end generate;

   GEN_LEVELS: for LVL in 0 to num_levels-1 generate
      constant num_of_mux  : integer := num_muxs(MUX_WIDTH, LVL);
      constant mod_of_mux  : integer := mod_muxs(MUX_WIDTH, LVL);

      signal tmp_ce_in     : std_logic;
      signal tmp_ce_sel    : std_logic;
      signal tmp_ce_out    : std_logic;
   begin
      GEN_FIRST_IN_TRUE: if(LVL = 0) generate
         GEN_CE: if(REG_IN = 1) generate
            tmp_ce_in      <= CE_IN;
            tmp_ce_sel     <= CE_IN;
         end generate;
         GEN_CE_OFF: if(REG_IN = 0) generate
            tmp_ce_in      <= '1';
            tmp_ce_sel     <= '1';
         end generate;

      end generate;
      GEN_FIRST_IN_FALSE: if(LVL /= 0) generate
         GEN_CE: if(REG_LVL = 1) generate
            tmp_ce_sel     <= CE_LVL;
         end generate;
         GEN_CE_OFF: if(REG_LVL = 0) generate
            tmp_ce_sel     <= '1';
         end generate;

         tmp_ce_in      <= '1';
      end generate;

      GEN_FIRST_OUT_TRUE: if(LVL = num_levels-1) generate
         GEN_CE: if(REG_OUT = 1) generate
            tmp_ce_out     <= CE_OUT;
         end generate;
         GEN_CE_OFF: if(REG_OUT = 0) generate
            tmp_ce_out     <= '1';
         end generate;
         DATA_OUT <= lvls_array(LVL+1)(0);
      end generate;

      GEN_FIRST_OUT_FALSE: if(LVL /= num_levels-1) generate
         GEN_CE: if(REG_LVL = 1) generate
            tmp_ce_out     <= CE_OUT;
         end generate;
         GEN_CE_OFF: if(REG_LVL = 0) generate
            tmp_ce_out     <= '1';
         end generate;
      end generate;

      GEN_MUXS: for MUXS in 0 to num_of_mux-1 generate
         constant pipe_in     : integer := gen_pipe_in(REG_IN, LVL);
         constant pipe_sel    : integer := gen_pipe_sel(REG_LVL, REG_IN, LVL);
         constant pipe_out    : integer := gen_pipe_out(LVL, num_levels-1, REG_OUT, REG_LVL);
         constant in_cascade  : boolean := gen_in_cascade(LVL);

         signal tmp_A         : std_logic_vector(DATA_WIDTH-1 downto 0);
         signal tmp_B         : std_logic_vector(DATA_WIDTH-1 downto 0);
         signal tmp_SEL       : std_logic_vector(0 downto 0);
      begin
         tmp_A <= lvls_array(LVL)(1+MUXS*2);
         GEN_CAS_OFF: if(in_cascade = false) generate
            tmp_B <= lvls_array(LVL)(MUXS*2);
         end generate;
         GEN_CAS_ON: if(in_cascade = true) generate
            tmp_B <= lvls_array_cas(LVL)(MUXS*2);
         end generate;

         GNE_PIPE_SEL: if(LVL > 0) generate
            SEL_PIPE_inst: entity work.PIPE_DSP
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

         GNE_PIPE_NO_SEL: if(LVL = 0) generate
            tmp_SEL <= SEL(LVL downto LVL);
         end generate;

         MUX_DSP_inst: entity work.MUX_DSP
         generic map (
            DATA_WIDTH => DATA_WIDTH,
            REG_IN_A   => pipe_in,
            REG_IN_B   => pipe_in,
            REG_SEL    => pipe_sel,
            REG_OUT    => pipe_out,
            EN_CASCADE_IN  => in_cascade,
            NEG_SEL        => true
         )
         port map (
            CLK   => CLK,
            RESET => RESET,
            A     => tmp_A,
            B     => tmp_B,
            CE_IN_A  => tmp_ce_in,
            CE_IN_B  => tmp_ce_in,
            CE_SEL   => tmp_ce_sel,
            SEL      => tmp_SEL(0),
            CE_OUT   => tmp_ce_out,
            P        => lvls_array(LVL+1)(MUXS),
            P_CAS    => lvls_array_cas(LVL+1)(MUXS)
         );
      end generate;

      GNE_LAST: if (mod_of_mux > 0) generate
         signal tmp_pipe : std_logic_vector(DATA_WIDTH-1 downto 0);
      begin
         process(CLK)
         begin
            if (CLK'event) and (CLK = '1') then
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
