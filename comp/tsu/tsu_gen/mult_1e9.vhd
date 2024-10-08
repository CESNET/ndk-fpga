-- mult_10e9.vhd: Mult 32bit number by 1e9 in DSP adders, return high 32 bits
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--
-- Copyright (C) 2015 CESNET
-- Author(s): Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;


architecture FULL of MULT_1E9 is

   signal zeros64    : std_logic_vector(63 downto 0);

   signal reg_din1   : std_logic_vector(31 downto 0);
   signal reg_din2   : std_logic_vector(31 downto 0);

   signal add1_a     : std_logic_vector(34 downto 0);
   signal add1_b     : std_logic_vector(34 downto 0);
   signal add2_a     : std_logic_vector(33 downto 0);
   signal add2_b     : std_logic_vector(33 downto 0);
   signal add4_a     : std_logic_vector(35 downto 0);
   signal add4_b     : std_logic_vector(35 downto 0);
   signal reg_add1   : std_logic_vector(34 downto 0);
   signal reg_add2   : std_logic_vector(33 downto 0);
   signal reg_add3   : std_logic_vector(34 downto 0);
   signal reg_add4   : std_logic_vector(35 downto 0);
   signal reg_add5   : std_logic_vector(33 downto 0);
   signal reg_add6   : std_logic_vector(33 downto 0);

   signal add7_a     : std_logic_vector(39 downto 0);
   signal add7_b     : std_logic_vector(39 downto 0);
   signal add8_a     : std_logic_vector(39 downto 0);
   signal add8_b     : std_logic_vector(39 downto 0);
   signal add9_a     : std_logic_vector(37 downto 0);
   signal add9_b     : std_logic_vector(37 downto 0);
   signal reg_add7   : std_logic_vector(39 downto 0);
   signal reg_add8   : std_logic_vector(39 downto 0);
   signal reg_add9   : std_logic_vector(37 downto 0);

   signal add10_a    : std_logic_vector(48 downto 0);
   signal add10_b    : std_logic_vector(48 downto 0);
   signal add11_a    : std_logic_vector(38 downto 0);
   signal add11_b    : std_logic_vector(38 downto 0);
   signal reg_add10  : std_logic_vector(48 downto 0);
   signal reg_add11  : std_logic_vector(38 downto 0);

   signal add12_a    : std_logic_vector(54 downto 0);
   signal add12_b    : std_logic_vector(54 downto 0);
   signal add12      : std_logic_vector(54 downto 0);
   signal reg_add12  : std_logic_vector(54 downto 0);


begin

   zeros64 <= X"0000000000000000";

   PIPE_inst: entity work.ALU_DSP
    generic map (
      DATA_WIDTH  => 32,
      REG_IN      => 1,
      REG_OUT     => 1
   )
   port map (
      CLK         => CLK,
      RESET       => '0',
      A           => DIN,
      B           => (others => '0'),
      CE_IN       => '1',
      CE_OUT      => '1',
      ALUMODE     => "0000",
      CARRY_IN    => '0',
      P           => reg_din2
   );

   --* Pipeline
   -- process(CLK)
   -- begin
   --   if CLK'event and CLK = '1' then
   --      -- Stage 1
   --      reg_din1 <= DIN;
   --      -- Stage 2
   --      reg_din2 <= reg_din1;
   --      -- Stage 3
   --      -- Stage 4
   --      reg_add12 <= add12;
   --   end if;
   -- end process;

   ---------------------------------------------
   -- How does this work?
   ---------------------------------------------

   -- 1E9 = 00111011 10011010 11001010 00000000 binary
   -- That is 13 ones.
   -- Bit weights: 9 11 14 15 17 19 20 23 24 25 27 28 29
   -- Bits 0-8 of the result will always be zeros.
   -- We will save bits by not storing those which can contain only zeros.
   -- We will hierarchically add and shift.
   -- >> and << in comments are bit shifts

   ---------------------------------------------
   -- First tree level - add neighbouring weights
   ---------------------------------------------

   -- add1 = (din<<9 + din<<11) >> 9
   -- 35 bits are needed for the result
   add1_a <= (zeros64(2 downto 0) & din);
   add1_b <= ("0" & din & zeros64(1 downto 0));
   ADD1_inst: entity work.ALU_DSP
   generic map (
      DATA_WIDTH  => 35,
      REG_IN      => 0,
      REG_OUT     => 1
   )
   port map (
      CLK         => CLK,
      RESET       => '0',
      A           => add1_a,
      B           => add1_b,
      CE_IN       => '1',
      CE_OUT      => '1',
      ALUMODE     => "0000",
      CARRY_IN    => '0',
      P           => reg_add1
   );

   -- add2 = (din<<14 + din<<15) >> 14
   -- 34 bits are needed for the result
   add2_a <= (zeros64(1 downto 0) & din);
   add2_b <= ("0" & din & zeros64(0 downto 0));
   ADD2_inst: entity work.ALU_DSP
   generic map (
      DATA_WIDTH  => 34,
      REG_IN      => 0,
      REG_OUT     => 1
   )
   port map (
      CLK         => CLK,
      RESET       => '0',
      A           => add2_a,
      B           => add2_b,
      CE_IN       => '1',
      CE_OUT      => '1',
      ALUMODE     => "0000",
      CARRY_IN    => '0',
      P           => reg_add2
   );

   -- add3 = (din<<17 + din<<19) >> 17
   -- 35 bits are needed for the result
   reg_add3 <= reg_add1;

   -- add4 = (din<<20 + din<<23) >> 20
   -- 36 bits are needed for the result
   add4_a <= (zeros64(3 downto 0) & din);
   add4_b <= ("0" & din & zeros64(2 downto 0));
   ADD4_inst: entity work.ALU_DSP
   generic map (
      DATA_WIDTH  => 36,
      REG_IN      => 0,
      REG_OUT     => 1
   )
   port map (
      CLK         => CLK,
      RESET       => '0',
      A           => add4_a,
      B           => add4_b,
      CE_IN       => '1',
      CE_OUT      => '1',
      ALUMODE     => "0000",
      CARRY_IN    => '0',
      P           => reg_add4
   );

   -- add5 = (din<<24 + din<<25) >> 24
   -- 34 bits are needed for the result
   reg_add5 <= reg_add2;

   -- add6 = (din<<27 + din<<28) >> 28
   -- 34 bits are needed for the result
   reg_add6 <= reg_add2;

   ---------------------------------------------
   -- End of first tree level. Note that only three different equations
   -- are used - synthetizer will optimize this level to three adders.
   -- Results are registered. If DSP slices are available, synthetizer may
   -- use registers embedded in DSP.
   ---------------------------------------------

   ---------------------------------------------
   -- Second tree level
   ---------------------------------------------

   -- add7 = ((din<<9 + din<<11)>>9 + (din<<14 + din<<15)>>14 << 5) >> 9
   --      = (din<<9 + din<<11 + din<<14 + din<<15) >> 9
   -- 40 bits are needed for the result
   add7_a <= (zeros64(4 downto 0) & reg_add1);
   add7_b <= ("0" & reg_add2 & zeros64(4 downto 0));
   ADD7_inst: entity work.ALU_DSP
   generic map (
      DATA_WIDTH  => 40,
      REG_IN      => 0,
      REG_OUT     => 1
   )
   port map (
      CLK         => CLK,
      RESET       => '0',
      A           => add7_a,
      B           => add7_b,
      CE_IN       => '1',
      CE_OUT      => '1',
      ALUMODE     => "0000",
      CARRY_IN    => '0',
      P           => reg_add7
   );

   -- add8 = (din<<17 + din<<19 + din<<20 din<<23) >> 17
   -- 40 bits are needed for the result
   add8_a <= (zeros64(4 downto 0) & reg_add3);
   add8_b <= ("0" & reg_add4 & zeros64(2 downto 0));
   ADD8_inst: entity work.ALU_DSP
   generic map (
      DATA_WIDTH  => 40,
      REG_IN      => 0,
      REG_OUT     => 1
   )
   port map (
      CLK         => CLK,
      RESET       => '0',
      A           => add8_a,
      B           => add8_b,
      CE_IN       => '1',
      CE_OUT      => '1',
      ALUMODE     => "0000",
      CARRY_IN    => '0',
      P           => reg_add8
   );

   -- add9 = (din<<24 + din<<25 + din<<27 din<<28) >> 24
   -- 38 bits are needed for the result
   add9_a <= (zeros64(3 downto 0) & reg_add5);
   add9_b <= ("0" & reg_add6 & zeros64(2 downto 0));
   ADD9_inst: entity work.ALU_DSP
   generic map (
      DATA_WIDTH  => 38,
      REG_IN      => 0,
      REG_OUT     => 1
   )
   port map (
      CLK         => CLK,
      RESET       => '0',
      A           => add9_a,
      B           => add9_b,
      CE_IN       => '1',
      CE_OUT      => '1',
      ALUMODE     => "0000",
      CARRY_IN    => '0',
      P           => reg_add9
   );

   ---------------------------------------------
   -- End of second tree level
   ---------------------------------------------

   ---------------------------------------------
   -- Third tree level
   ---------------------------------------------

   -- add10 = (din<<9 + din<<11 + din<<14 + din<<15 +
   --          din<<17 + din<<19 + din<<20 + din<<23) >> 9
   -- 49 bits are needed for the result
   add10_a <= (zeros64(8 downto 0) & reg_add7);
   add10_b <= ("0" & reg_add8 & zeros64(7 downto 0));
   ADD10_inst: entity work.ALU_DSP
   generic map (
      DATA_WIDTH  => 49,
      REG_IN      => 0,
      REG_OUT     => 1
   )
   port map (
      CLK         => CLK,
      RESET       => '0',
      A           => add10_a,
      B           => add10_b,
      CE_IN       => '1',
      CE_OUT      => '1',
      ALUMODE     => "0000",
      CARRY_IN    => '0',
      P           => reg_add10
   );

   -- add11 = (din<<24 + din<<25 + din<<27 + din<<28) >> 24 + din<<5
   -- add11 = (din<<24 + din<<25 + din<<27 + din<<28) >> 24 + din<<29 >> 24
   -- add11 = (din<<24 + din<<25 + din<<27 + din<<28 + din<<29) >> 24
   -- 39 bits are needed for the result
   add11_a <= (zeros64(0 downto 0) & reg_add9);
   add11_b <= (zeros64(1 downto 0) & reg_din2 & zeros64(4 downto 0));
   ADD11_inst: entity work.ALU_DSP
   generic map (
      DATA_WIDTH  => 39,
      REG_IN      => 0,
      REG_OUT     => 1
   )
   port map (
      CLK         => CLK,
      RESET       => '0',
      A           => add11_a,
      B           => add11_b,
      CE_IN       => '1',
      CE_OUT      => '1',
      ALUMODE     => "0000",
      CARRY_IN    => '0',
      P           => reg_add11
   );

   ---------------------------------------------
   -- End of third tree level
   ---------------------------------------------

   ---------------------------------------------
   -- Fourh tree level
   ---------------------------------------------

   -- add12 = (din<<9 + din<<11 + din<<14 + din<<15 +
   --          din<<17 + din<<19 + din<<20 + din<<23) >> 9
   --         (din<<24 + din<<25 + din<<27 + din<<28 + din<<29)>>24 << 15
   -- add12 = (din<<9 + din<<11 + din<<14 + din<<15 + din<<17 + din<<19 +
   --          din<<20 + din<<23 + din<<24 + din<<25 + din<<27 + din<<28 +
   --          din<<29) >> 9
   -- 55 bits are needed

   add12_a <= (zeros64(5 downto 0) & reg_add10);
   add12_b <= ("0" & reg_add11 & zeros64(14 downto 0));
   ADD12_inst: entity work.ALU_DSP
   generic map (
      DATA_WIDTH  => 55,
      REG_IN      => 0,
      REG_OUT     => 1
   )
   port map (
      CLK         => CLK,
      RESET       => '0',
      A           => add12_a,
      B           => add12_b,
      CE_IN       => '1',
      CE_OUT      => '1',
      ALUMODE     => "0000",
      CARRY_IN    => '0',
      P           => reg_add12
   );

   ---------------------------------------------
   -- End of fourth tree level
   ---------------------------------------------

   -- reg_add12 contains the result shifted 9 bits left.
   -- We will ignore another 23 bits in our application, which leaves us with
   -- nice 32 bits of result.
   dout <= reg_add12(54 downto 23);

end architecture;
