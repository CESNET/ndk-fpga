-- n_one.vhd : Implementation of n one detector
--!
--! \file
--! \brief Implementation of n one detector
--! \Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--! \date 2016
--!
--! \section License
--!
--! Copyright (C) 2016 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;
use work.math_pack.all;
use work.type_pack.all;

architecture FULL of N_ONE is

   constant DATA_WIDTH_EXT : integer := 2**max(log2(DATA_WIDTH),1);
   constant STAGES         : natural := log2(DATA_WIDTH_EXT/2);

   signal d_ext         : std_logic_vector(DATA_WIDTH_EXT-1 downto 0);
   signal d_arr         : slv_array_2d_t(STAGES downto 0)(DATA_WIDTH_EXT-1 downto 0)(DATA_WIDTH_EXT-1 downto 0);
   signal n_arr         : slv_array_2d_t(STAGES downto 0)(DATA_WIDTH_EXT-1 downto 0)(log2(DATA_WIDTH_EXT)-1 downto 0);
   signal a_arr         : slv_array_2d_t(STAGES downto 0)(DATA_WIDTH_EXT-1 downto 0)(log2(DATA_WIDTH_EXT)-1 downto 0);
   signal v_arr         : slv_array_t(STAGES downto 0)(DATA_WIDTH_EXT-1 downto 0);

begin

   d_ext0g: if DATA_WIDTH_EXT = DATA_WIDTH generate
      d_ext <= D;
   end generate;

   d_ext1g: if DATA_WIDTH_EXT /= DATA_WIDTH generate
      d_ext(DATA_WIDTH-1 downto 0) <= D;
      d_ext2g: for i in DATA_WIDTH to DATA_WIDTH_EXT-1 generate
         d_ext(i) <= '0';
      end generate;
   end generate;

   core_g: if DATA_WIDTH_EXT = 2 generate
      core_i: entity work.N_ONE_CORE
      port map(
         D   => d_ext,
         N   => N(0),
         A   => A(0),
         VLD => VLD
      );
   end generate;

   tree_g: if DATA_WIDTH_EXT /= 2 generate
      d_arr(0)(0) <= d_ext;
      n_arr(0)(0) <= N;

      st_g: for i in 0 to STAGES-1 generate
         constant STAGE_ITEMS : natural := 2**i;
         constant STAGE_WIDTH : natural := DATA_WIDTH_EXT/STAGE_ITEMS;
      begin
         sti_g: for j in 0 to STAGE_ITEMS-1 generate
            itm_i : entity work.N_ONE_LOGIC
            generic map(
               DATA_WIDTH => STAGE_WIDTH
            )
            port map(
               D       => d_arr(i)(j)(STAGE_WIDTH-1 downto 0),
               N       => n_arr(i)(j)(log2(STAGE_WIDTH)-1 downto 0),
               A       => a_arr(i)(j)(log2(STAGE_WIDTH)-1 downto 0),
               VLD     => v_arr(i)(j),
               D_NEXT0 => d_arr(i+1)(j*2)(STAGE_WIDTH/2-1 downto 0),
               N_NEXT0 => n_arr(i+1)(j*2)(log2(STAGE_WIDTH/2)-1 downto 0),
               A_NEXT0 => a_arr(i+1)(j*2)(log2(STAGE_WIDTH/2)-1 downto 0),
               D_NEXT1 => d_arr(i+1)(j*2+1)(STAGE_WIDTH/2-1 downto 0),
               N_NEXT1 => n_arr(i+1)(j*2+1)(log2(STAGE_WIDTH/2)-1 downto 0),
               A_NEXT1 => a_arr(i+1)(j*2+1)(log2(STAGE_WIDTH/2)-1 downto 0)
            );
         end generate;
      end generate;

      A   <= a_arr(0)(0);
      VLD <= v_arr(0)(0);
   end generate;

end architecture;
