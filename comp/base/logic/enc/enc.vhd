-- gen_enc.vhd : Implementation of n one detector
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
use ieee.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

architecture full of gen_enc is

   component gen_enc
   generic (
      --! \brief Data width of input vector
      ITEMS           : integer;
      DEVICE          : string
   );
   port (
      --! \name Input vector
      --! --------------------------------------------------------------------------
      DI                 : in  std_logic_vector(ITEMS-1 downto 0);
      --! \name Output address
      --! --------------------------------------------------------------------------
      ADDR                 : out std_logic_vector(max(log2(ITEMS),1)-1 downto 0)
   );
   end component;

   constant ITEMS_EXT : integer := 2**max(log2(ITEMS),1);
   constant STAGES    : natural := log2(ITEMS_EXT/2);

   signal d_ext       : std_logic_vector(ITEMS_EXT-1 downto 0);
   signal d_arr       : slv_array_2d_t(STAGES downto 0)(ITEMS_EXT-1 downto 0)(ITEMS_EXT-1 downto 0);
   signal a_arr       : slv_array_2d_t(STAGES downto 0)(ITEMS_EXT-1 downto 0)(log2(ITEMS_EXT)-1 downto 0);

   --! -------------------------------------------------------------------------

begin

   d_ext0g: if ITEMS_EXT = ITEMS generate
      d_ext <= DI;
   end generate;

   d_ext1g: if ITEMS_EXT /= ITEMS generate
      d_ext(ITEMS-1 downto 0) <= DI;
      d_ext2g: for i in ITEMS to ITEMS_EXT-1 generate
         d_ext(i) <= '0';
      end generate;
   end generate;

   gen_enc0g: if ITEMS = 1 generate
      ADDR <= (others => '0');
   end generate;

   gen_enc1g: if ITEMS /= 1 and ITEMS_EXT = 2 generate
      ADDR(0) <= d_ext(1);
   end generate;

   gen_enc2g: if ITEMS_EXT /= 2 generate
      d_arr(0)(0) <= d_ext;

      st_g: for i in 0 to STAGES-1 generate
         constant STAGE_ITEMS : natural := 2**i;
         constant STAGE_WIDTH : natural := ITEMS_EXT/STAGE_ITEMS;
      begin
         sti_g: for j in 0 to STAGE_ITEMS-1 generate
            itm_i : entity work.GEN_ENC_LOGIC
            generic map(
               ITEMS  => STAGE_WIDTH,
               DEVICE => DEVICE
            )
            port map(
               DI      => d_arr(i)(j)(STAGE_WIDTH-1 downto 0),
               ADDR    => a_arr(i)(j)(log2(STAGE_WIDTH)-1 downto 0),
               D_NEXT0 => d_arr(i+1)(j*2)(STAGE_WIDTH/2-1 downto 0),
               A_NEXT0 => a_arr(i+1)(j*2)(log2(STAGE_WIDTH/2)-1 downto 0),
               D_NEXT1 => d_arr(i+1)(j*2+1)(STAGE_WIDTH/2-1 downto 0),
               A_NEXT1 => a_arr(i+1)(j*2+1)(log2(STAGE_WIDTH/2)-1 downto 0)
            );
         end generate;
      end generate;

      ADDR <= a_arr(0)(0);
   end generate;

end full;
