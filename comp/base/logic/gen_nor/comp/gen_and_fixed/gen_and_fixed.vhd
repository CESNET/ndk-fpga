-- gen_and.vhd
--!
--! \file
--! \brief Generic AND.
--! \author Vaclav Hummel <vaclav.hummel@cesnet.cz>
--! \date 2017
--!
--! \section License
--!
--! Copyright (C) 2012 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use IEEE.math_real.all;
use work.math_pack.all;
use work.type_pack.all;


--! \brief Behavioral implementation of generic AND.
architecture behav of GEN_AND_FIXED is

   constant DATA_WIDTH_EXT : integer := integer(ceil(real(DATA_WIDTH)/6.0))*6;

   signal di_ext : std_logic_vector(DATA_WIDTH_EXT-1 downto 0);
   signal di_deser : slv_array_t(0 to DATA_WIDTH_EXT/6-1)(6-1 downto 0);
   signal di_red : std_logic_vector(DATA_WIDTH_EXT/6-1 downto 0);
   signal carry_chain_do : std_logic_vector(DATA_WIDTH_EXT/6-1 downto 0);

begin

   gen_andg: if DATA_WIDTH <= 6 or (DEVICE /= "ULTRASCALE" and DEVICE /= "7SERIES" and DEVICE /= "VIRTEX6") generate
      DO <= and DI;
   end generate;

   gen_andgg: if (DEVICE = "ULTRASCALE" or DEVICE = "7SERIES" or DEVICE = "VIRTEX6") and DATA_WIDTH > 6 generate

      di_ext(DATA_WIDTH-1 downto 0) <= DI;

      di_extg: if DATA_WIDTH /= DATA_WIDTH_EXT generate
         di_ext(DATA_WIDTH_EXT-1 downto DATA_WIDTH) <= (others => '1');
      end generate;

      di_deser <= slv_array_to_deser(di_ext, DATA_WIDTH_EXT/6, 6);

      di_redg: for i in 0 to DATA_WIDTH_EXT/6-1 generate
         di_red(i) <= (and di_deser(i));
      end generate;

      carry_chaini: entity work.CARRY_CHAIN
      generic map(
         CARRY_WIDTH => DATA_WIDTH_EXT/6,
         DEVICE => DEVICE
      )
      port map(
         -- Initial input carry
         CI => '1',
         -- Data input (AX/BX/CX/DX or O5 from LUT)
         DI => (others => '0'),
         -- Carry selection input (O6 from LUT)
         S => di_red,
         -- Carry output
         --     CO(-1) = CI
         --     CO(i) = CO(i-1) when S(i) = '1' else DI(i);
         CO => carry_chain_do,
         -- Data output
         --     DO(i) = CO(i-1) xor S(i)
         DO => open
      );

      DO <= carry_chain_do(DATA_WIDTH_EXT/6-1);

   end generate;

end architecture;

