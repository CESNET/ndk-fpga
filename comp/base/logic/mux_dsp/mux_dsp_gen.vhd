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

entity MUX_DSP_GEN is
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

architecture full of MUX_DSP_GEN is
   constant new_data_width : integer := func_new_data_width(DATA_WIDTH);

   signal tmp_data_in   : std_logic_vector(new_data_width*MUX_WIDTH-1 downto 0);
   signal tmp_data_out  : std_logic_vector(new_data_width-1 downto 0);
begin

   GEN_INPUT_DATA: if (new_data_width /= DATA_WIDTH) generate
      GEN_INPUT: for I in 0 to MUX_WIDTH-1 generate
         signal sel_input : std_logic_vector(new_data_width-1 downto 0);
      begin
         sel_input(DATA_WIDTH-1 downto 0) <= DATA_IN(DATA_WIDTH+(I*DATA_WIDTH)-1 downto (I*DATA_WIDTH));
         sel_input(new_data_width-1 downto DATA_WIDTH) <= (others => '0');
         tmp_data_in(new_data_width+(I*new_data_width)-1 downto (I*new_data_width)) <= sel_input;
      end generate;
   end generate;

   GEN_INPUT_DATA_OFF: if (new_data_width = DATA_WIDTH) generate
      tmp_data_in <= DATA_IN;
   end generate;

   MUX_LOW_inst: entity work.MUX_DSP_GEN_LOW
   generic map(
      DATA_WIDTH  => new_data_width,
      MUX_WIDTH   => MUX_WIDTH,
      REG_IN      => REG_IN,
      REG_OUT     => REG_OUT,
      REG_LVL     => REG_LVL
   )
   port map(
      CLK      => CLK,
      RESET    => RESET,
      DATA_IN  => tmp_data_in,
      CE_IN    => CE_IN,
      CE_OUT   => CE_OUT,
      CE_LVL   => CE_LVL,
      SEL      => SEL,
      DATA_OUT => tmp_data_out
   );

   DATA_OUT <= tmp_data_out(DATA_WIDTH-1 downto 0);
end architecture;
