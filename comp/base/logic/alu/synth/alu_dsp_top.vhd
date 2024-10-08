--! alu_dsp_top.vhd
--!
--! \file
--! \brief ALU  implemented with Virtex-7 DSP slice
--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
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
entity ALU_DSP_TOP is
   generic (
      DATA_WIDTH  : integer := 96;
      --! Input pipeline registers (0, 1)
      REG_IN      : integer := 1;
      --! Output pipeline register (0, 1)
      REG_OUT     : integer := 1
      );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;
      --! Data input
      A        : in  std_logic_vector((DATA_WIDTH - 1) downto 0);
      --! Data input
      B        : in  std_logic_vector((DATA_WIDTH - 1) downto 0);
      --! Clock enable for input pipeline registers
      CE_IN    : in  std_logic;
      --! Clock enable for output pipeline registers
      CE_OUT   : in  std_logic;

      --! control alu
      --! operators (A [operator] B):
      --!     "0000" -> ADD
      --!
      --!     "0001" -> SUB (A - (B + CARRY_IN))
      --!     (WARNING for SUB: when "DATA_WIDTH <= 48" or "DATA_WIDTH mod 48 = 0"
      --!      CARRY_OUT is inverted)
      --!
      --!     "0010" -> NAND
      --!     "0011" -> AND
      --!     "0100" -> OR
      --!     "0101" -> NOR
      --!     "0110" -> XOR
      --!     "0111" -> XNOR
      --! operators and negated data inputs:
      --!     "1000" -> B AND (NOT A)
      --!     "1001" -> (NOT B) ADD A
      --!     "1010" -> B OR (NOT A)
      --!     "1011" -> (NOT B) OR A
      ALUMODE   : in std_logic_vector(3 downto 0);

      --! carry input
      CARRY_IN  : in std_logic;
      --! carry output
      CARRY_OUT : out std_logic;
      --! Data output
      --! Latency = REG_IN + REG_OUT
      P         : out std_logic_vector((DATA_WIDTH - 1) downto 0)
     );
end ALU_DSP_TOP;

--! Vitrex-7 architecture of ALU_DSP
architecture V7_DSP_TOP of ALU_DSP_TOP is

   --! signals
   signal reset_D     : std_logic;
   signal a_D         : std_logic_vector((DATA_WIDTH - 1) downto 0);
   signal b_D         : std_logic_vector((DATA_WIDTH - 1) downto 0);
   signal ce_in_D     : std_logic;
   signal ce_out_D    : std_logic;
   signal alumode_D   : std_logic_vector(3 downto 0);
   signal carry_in_D  : std_logic;
   signal carry_out_D : std_logic;
   signal p_D         : std_logic_vector((DATA_WIDTH - 1) downto 0);

begin

   uut : entity work.ALU_DSP(structural)
   generic map (
      DATA_WIDTH  => DATA_WIDTH,
      REG_IN      => REG_IN,
      REG_OUT     => REG_OUT
   )
   port map (
      CLK         => CLK,
      RESET       => reset_D,
      A           => a_D,
      B           => b_D,
      CE_IN       => ce_in_D,
      CE_OUT      => ce_out_D,
      ALUMODE     => alumode_D,
      CARRY_IN    => carry_in_D,
      CARRY_OUT   => carry_out_D,
      P           => p_D
   );

    -- input registers
   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if (RESET='1') then
            reset_D <= '1';
            a_D <= (others => '0');
            b_D <= (others => '0');
            ce_in_D <= '0';
            ce_out_D <= '0';
            alumode_D <= (others => '0');
            carry_in_D <= '0';
         else
            reset_D <= '0';
            a_D <= A;
            b_D <= B;
            ce_in_D <= CE_IN;
            ce_out_D <= CE_OUT;
            alumode_D <= ALUMODE;
            carry_in_D <= CARRY_IN;
         end if;
      end if;
    end process;

   -- output registers
   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if (RESET='1') then
            CARRY_OUT <= '0';
            P <= (others => '0');
         else
            CARRY_OUT <= carry_out_D;
            P <= p_D;
         end if;
      end if;
   end process;
end V7_DSP_TOP;
