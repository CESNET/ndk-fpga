-- n_one_logic.vhd : Implementation of n one detector
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
use ieee.std_logic_arith.all;
use work.math_pack.all;

entity N_ONE_LOGIC is
   generic (
      -- Data width of input vector, minimum is 4, must be power of two
      DATA_WIDTH : integer := 4
   );
   port (
      -- Input vector
      D                 : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      -- N one number from zero
      N                 : in  std_logic_vector(log2(DATA_WIDTH)-1 downto 0);
      -- Output address
      A                 : out std_logic_vector(log2(DATA_WIDTH)-1 downto 0);
      VLD               : out std_logic;

      D_NEXT0            : out std_logic_vector((DATA_WIDTH/2)-1 downto 0);
      N_NEXT0            : out std_logic_vector(log2(DATA_WIDTH/2)-1 downto 0);
      A_NEXT0            : in  std_logic_vector(log2(DATA_WIDTH/2)-1 downto 0);

      D_NEXT1            : out std_logic_vector((DATA_WIDTH/2)-1 downto 0);
      N_NEXT1            : out std_logic_vector(log2(DATA_WIDTH/2)-1 downto 0);
      A_NEXT1            : in  std_logic_vector(log2(DATA_WIDTH/2)-1 downto 0)
   );
end entity;

architecture FULL of N_ONE_LOGIC is

   signal sum           : std_logic_vector(log2(DATA_WIDTH/2) downto 0);
   signal sub_a         : std_logic_vector(log2(DATA_WIDTH) downto 0);
   signal sub_b         : std_logic_vector(log2(DATA_WIDTH) downto 0);
   signal sub           : std_logic_vector(log2(DATA_WIDTH) downto 0);
   signal sub_cmp       : std_logic;
   signal sum_all0      : std_logic_vector(log2(DATA_WIDTH/2) downto 0);
   signal sum_all       : unsigned(log2(DATA_WIDTH) downto 0);
   signal mux_in        : std_logic_vector(max(log2(DATA_WIDTH/2)*2, 1)-1 downto 0);

begin

   --! Sum of first half of vector computation ---------------------------------

   sump: process(D(DATA_WIDTH/2-1 downto 0))
      variable b : unsigned(log2(DATA_WIDTH/2) downto 0);
   begin
      b := (others => '0');
      for i in 0 to DATA_WIDTH/2-1 loop
         b := b + unsigned(D(i downto i));
      end loop;
      sum <= std_logic_vector(b);
   end process;

   --! -------------------------------------------------------------------------

   --! Subtranction ------------------------------------------------------------

   sub_a <= "0" & N;
   sub_b <= "0" & sum;

   sub <= signed(sub_a) - signed(sub_b);

   sub_cmp <= '0' when (signed(sub) < 0) else
               '1';

   --! VLD generation ----------------------------------------------------------

   sum_allp: process(D)
      variable b : unsigned(log2(DATA_WIDTH/2) downto 0);
   begin
      b := (others => '0');
      for i in DATA_WIDTH/2 to DATA_WIDTH-1 loop
         b := b + unsigned(D(i downto i));
      end loop;
      sum_all0 <= std_logic_vector(b);
   end process;

   sum_all <= unsigned(sum_all0) + unsigned('0' & sum);

   VLD <= '1' when(sum_all > unsigned(N)) else
            '0';

   --! Output address assignment -----------------------------------------------

   core_g : if DATA_WIDTH/2 = 2 generate
      core0_i: entity work.N_ONE_CORE
      port map(
         D   => D(DATA_WIDTH/2-1 downto 0),
         N   => N(0),
         A   => mux_in(0),
         VLD => open
      );

      core1_i: entity work.N_ONE_CORE
      port map(
         D   => D(DATA_WIDTH-1 downto DATA_WIDTH/2),
         N   => sub(0),
         A   => mux_in(1),
         VLD => open
      );

      D_NEXT1 <= (others => '0');
      N_NEXT1 <= (others => '0');

      D_NEXT0 <= (others => '0');
      N_NEXT0 <= (others => '0');
   end generate;

   wire_g : if DATA_WIDTH/2 /= 2 generate
      D_NEXT1 <= D(DATA_WIDTH-1 downto DATA_WIDTH/2);
      N_NEXT1 <= sub(log2(DATA_WIDTH/2)-1 downto 0);

      D_NEXT0 <= D(DATA_WIDTH/2-1 downto 0);
      N_NEXT0 <= N(log2(DATA_WIDTH/2)-1 downto 0);

      mux_in <= A_NEXT1 & A_NEXT0;
   end generate;

   A(log2(DATA_WIDTH)-1) <= sub_cmp;

   mux_i: entity work.GEN_MUX
   generic map(
      DATA_WIDTH => log2(DATA_WIDTH/2),
      MUX_WIDTH => 2
   )
   port map(
      DATA_IN => mux_in,
      SEL(0) => sub_cmp,
      DATA_OUT => A(log2(DATA_WIDTH/2)-1 downto 0)
   );

end architecture;
