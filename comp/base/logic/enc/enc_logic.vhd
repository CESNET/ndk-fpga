-- gen_enc_logic.vhd : Entity of n one detector
--!
--! \file
--! \brief Entity of n one detector
--! \author Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
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

entity GEN_ENC_LOGIC is
   generic (
      --! \brief Data width of input vector
      ITEMS  : integer := 4096;
      DEVICE : string  := "none"
   );
   port (
      DI      : in  std_logic_vector(ITEMS-1 downto 0);
      ADDR    : out std_logic_vector(log2(ITEMS)-1 downto 0);

      D_NEXT0 : out std_logic_vector((ITEMS/2)-1 downto 0);
      A_NEXT0 : in  std_logic_vector(log2(ITEMS/2)-1 downto 0);

      D_NEXT1 : out std_logic_vector((ITEMS/2)-1 downto 0);
      A_NEXT1 : in  std_logic_vector(log2(ITEMS/2)-1 downto 0)
   );
end entity;

architecture FULL of GEN_ENC_LOGIC is

   signal sub_cmp : std_logic;
   signal a0      : std_logic_vector(max(log2(ITEMS/2), 1)-1 downto 0);
   signal a1      : std_logic_vector(max(log2(ITEMS/2), 1)-1 downto 0);

begin

   --! Subtranction ------------------------------------------------------------
   gen_nori: entity work.GEN_NOR
   generic map(
      DATA_WIDTH => ITEMS/2,
      DEVICE     => DEVICE
   )
   port map(
      DI => DI(ITEMS-1 downto ITEMS/2),
      DO => sub_cmp
   );

   --! Core logic assignment ---------------------------------------------------

   core_g: if (ITEMS/2) = 2 generate
      a0(0) <= DI(1);
      a1(0) <= DI(1+(ITEMS/2));
   end generate;

   core_out_g: if (ITEMS/2) /= 2 generate
      D_NEXT0 <= DI(ITEMS/2-1 downto 0);
      a0      <= A_NEXT0;

      D_NEXT1 <= DI(ITEMS-1 downto ITEMS/2);
      a1      <= A_NEXT1;
   end generate;

   --! Output address assignment -----------------------------------------------
   ADDR(log2(ITEMS)-1) <= not sub_cmp;
   ADDR(log2(ITEMS/2)-1 downto 0) <= a1 when (sub_cmp = '0') else a0;

end architecture;
