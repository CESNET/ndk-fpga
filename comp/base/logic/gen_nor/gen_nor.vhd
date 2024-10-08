-- gen_nor.vhd
--!
--! \file
--! \brief Generic NOR.
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


--! \brief Behavioral implementation of generic OR.
architecture behav of GEN_NOR is

   constant DATA_WIDTH_EXT : integer := integer(ceil(real(DATA_WIDTH)/6.0))*6;
   constant DATA_WIDTH_ULTRASCALE : integer := integer(ceil(real(DATA_WIDTH)/48.0))*48;

   signal di_ext : std_logic_vector(DATA_WIDTH_EXT-1 downto 0);
   signal di_deser : slv_array_t(0 to DATA_WIDTH_EXT/6-1)(6-1 downto 0);
   signal di_red : std_logic_vector(DATA_WIDTH_EXT/6-1 downto 0);
   signal carry_chain_do : std_logic_vector(DATA_WIDTH_EXT/6-1 downto 0);

   signal di_ultrascale : std_logic_vector(DATA_WIDTH_ULTRASCALE-1 downto 0);
   signal di_ultrascale_deser : slv_array_t(0 to DATA_WIDTH_ULTRASCALE/48-1)(48-1 downto 0);
   signal di_ultrascale_red : std_logic_vector(DATA_WIDTH_ULTRASCALE/48-1 downto 0);

begin

   gen_norg: if DATA_WIDTH <= 6 or (DEVICE /= "ULTRASCALE" and DEVICE /= "7SERIES" and DEVICE /= "VIRTEX6") generate
      DO <= nor DI;
   end generate;

   gen_norgg: if DEVICE = "ULTRASCALE" or DEVICE = "7SERIES" or DEVICE = "VIRTEX6" generate

      gen_norggg: if DATA_WIDTH > 6 and DATA_WIDTH <= 48 generate

         di_ext(DATA_WIDTH-1 downto 0) <= DI;

         di_extg: if DATA_WIDTH /= DATA_WIDTH_EXT generate
            di_ext(DATA_WIDTH_EXT-1 downto DATA_WIDTH) <= (others => '0');
         end generate;

         doi: entity work.GEN_NOR_FIXED
         generic map(
            --! \brief Width of input signal, number of bits to NOR.
            --! \details Must be greater than 0.
            DATA_WIDTH => DATA_WIDTH_EXT,
            DEVICE => DEVICE
         )
         port map(
            --! Input data, vector of bits to OR.
            DI => di_ext,
            --! Output data, result of OR.
            DO => DO
         );

      end generate;

      gen_norgggg: if DATA_WIDTH > 48 generate
         di_ultrascale(DATA_WIDTH-1 downto 0) <= DI;

         di_ultrascaleg: if DATA_WIDTH /= DATA_WIDTH_ULTRASCALE generate
            di_ultrascale(DATA_WIDTH_ULTRASCALE-1 downto DATA_WIDTH) <= (others => '0');
         end generate;

         di_ultrascale_deser <= slv_array_to_deser(di_ultrascale, DATA_WIDTH_ULTRASCALE/48, 48);

         di_ultrascale_redg: for i in 0 to DATA_WIDTH_ULTRASCALE/48-1 generate
            di_ultrascale_redi: entity work.GEN_NOR_FIXED
            generic map(
               --! \brief Width of input signal, number of bits to NOR.
               --! \details Must be greater than 0.
               DATA_WIDTH => 48,
               DEVICE => DEVICE
            )
            port map(
               --! Input data, vector of bits to OR.
               DI => di_ultrascale_deser(i),
               --! Output data, result of OR.
               DO => di_ultrascale_red(i)
            );
         end generate;

         doi: entity work.GEN_AND_FIXED
         generic map(
            --! \brief Width of input signal, number of bits to NOR.
            --! \details Must be greater than 0.
            DATA_WIDTH => DATA_WIDTH_ULTRASCALE/48,
            DEVICE => DEVICE
         )
         port map(
            --! Input data, vector of bits to OR.
            DI => di_ultrascale_red,
            --! Output data, result of OR.
            DO => DO
         );

      end generate;

   end generate;

end architecture;

