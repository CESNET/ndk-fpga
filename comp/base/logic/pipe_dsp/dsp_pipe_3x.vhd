--! dps_pipe_3x.vhd
--!
--! \file
--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--!
--! \section License
--!
--! Copyright (C) 2015 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
Library UNISIM;
use UNISIM.vcomponents.all;

--! \brief DSP slice ALU entity
entity DSP_PIPE_3x is
   generic (
      DATA_WIDTH  : integer := 48;
      --! number of registers, max 3
      NUM_REGS    : integer := 1
   );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;
      --! clock enbale for registres
      CE       : in std_logic;
      --! input data
      DATA_IN  : in std_logic_vector(DATA_WIDTH-1 downto 0);
      --! output data
      DATA_OUT : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end entity;

architecture full of DSP_PIPE_3x is
begin

   DSP_REG: for I in 0 to (DATA_WIDTH/48)-1 generate
      DSP_PIPE_3x48_inst: entity work.DSP_PIPE_3x48
         generic map(
            NUM_REGS => NUM_REGS
         )
         port map (
            CLK => CLK,
            RESET => RESET,
            DATA_IN => DATA_IN(47 + (I * 48) downto 0 + (I * 48)),
            DATA_OUT => DATA_OUT(47 + (I * 48) downto 0 + (I * 48)),
            CE => CE
         );
   end generate;

  DSP_REG_MOD: if (DATA_WIDTH mod 48 > 0) generate
      signal Amod : std_logic_vector(47 downto 0);
      signal Pmod : std_logic_vector(47 downto 0);
   begin
      Amod((DATA_WIDTH mod 48)-1 downto 0) <= DATA_IN(DATA_IN'LENGTH-1 downto DATA_IN'LENGTH-(DATA_WIDTH mod 48));
      Amod(47 downto (DATA_WIDTH mod 48)) <= (others => '0');
      DATA_OUT(DATA_OUT'LENGTH-1 downto DATA_OUT'LENGTH-(DATA_WIDTH mod 48)) <= Pmod((DATA_WIDTH mod 48)-1 downto 0);

      DSP_PIPE_3x48_inst: entity work.DSP_PIPE_3x48
         generic map(
            NUM_REGS => NUM_REGS
         )
         port map (
            CLK => CLK,
            RESET => RESET,
            DATA_IN => Amod,
            DATA_OUT => Pmod,
            CE => CE
         );
   end generate;
end architecture;
