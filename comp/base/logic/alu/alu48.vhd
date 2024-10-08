--! alu48.vhd
--!
--! \file
--! \brief ALU implemented with Virtex-7 DSP slice
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
entity ALU48 is
   generic (
      --! Input pipeline registers (0, 1)
      REG_IN         : integer := 0;
      --! Output pipeline register (0, 1)
      REG_OUT        : integer := 0;
      --! 1 => carry_cas_in, 0 => carr_in
      SWITCH_CARRY      : integer := 0;
      SWITCH_CARRY_OUT  : integer := 0
   );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;
      --! Data input
      A        : in  std_logic_vector(47 downto 0);
      --! Data input
      B        : in  std_logic_vector(47 downto 0);
      --! Clock enable for input pipeline registers
      CE_IN    : in  std_logic;
      --! Clock enable for output pipeline registers
      CE_OUT   : in  std_logic;

      --! control alu
      --! operators (A [operator] B):
      --!     "0000" -> ADD (A + B + CARRY_IN)
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
      --!     "1001" -> (NOT B) AND A
      --!     "1010" -> B OR (NOT A)
      --!     "1011" -> (NOT B) OR A
      ALUMODE     : in std_logic_vector(3 downto 0);

      --! carry input
      CARRY_IN    : in std_logic;
      --! carry output
      CARRY_OUT   : out std_logic;
      --! Data output
      --! Latency = REG_IN + REG_OUT
      P           : out std_logic_vector(47 downto 0)
     );
end ALU48;

--! Vitrex-7 architecture of ALU48
architecture V7_DSP of ALU48 is

   --! signals
   signal zeros   : std_logic_vector(63 downto 0);
   signal mode    : std_logic_vector(3 downto 0);
   signal op_mode : std_logic_vector(6 downto 0);

   signal carryinsel : std_logic_vector(2 downto 0);
   signal carry_cas  : std_logic;
   signal carry      : std_logic;

   signal out_carry     : std_logic_vector(3 downto 0);
   signal out_cas_carry : std_logic;

begin
   --! generate connection carryin
   --GEN_CARRY: if(SWITCH_CARRY = 0) generate
      carryinsel <= "000";
      carry_cas  <= '0';
      carry      <= CARRY_IN;
   --end generate;

   --! generate connection carryin cascade
   --GEN_CARRY_CAS: if(SWITCH_CARRY = 1) generate
   --   carryinsel <= "010";
   --   carry_cas  <= CARRY_IN;
   --   carry      <= '0';
   --end generate;

   --! generate connection carryout
   --GEN_CARRY_OUT: if(SWITCH_CARRY_OUT = 0) generate
      CARRY_OUT <= out_carry(3);
   --end generate;

   ----! generate connection carryout cascade
   --GEN_CARRY_CAS_OUT: if(SWITCH_CARRY_OUT = 1) generate
   --   CARRY_OUT <= out_cas_carry;
   --end generate;

   WITH ALUMODE SELECT
      mode <= "0000" WHEN "0000",   -- +
              "0011" WHEN "0001",   -- -
              "1110" WHEN "0010",   --NAND
              "1100" WHEN "0011",   --AND
              "1100" WHEN "0100",   --OR
              "1110" WHEN "0101",   --NOR
              "0100" WHEN "0110",   --XOR
              "0101" WHEN "0111",   --XNOR
              "1101" WHEN "1000",   --X AND (NOT Z)
              "1111" WHEN "1001",   --(NOT X) AND Z
              "1101" WHEN "1010",   --X OR (NOT Z)
              "1111" WHEN "1011",   --(NOT X) OR Z
              "XXXX" WHEN OTHERS;

   WITH ALUMODE SELECT
      op_mode <= "0111011" WHEN "0100",
                 "0111011" WHEN "0101",
                 "0111011" WHEN "1001",
                 "0111011" WHEN "1010",
                 "0110011" WHEN OTHERS;

   zeros <= X"0000000000000000";

   GEN_ALU_DSP: if (REG_IN = 0 OR REG_IN = 1) generate
       --! DSP slice instantion
       DSP48E1_inst : DSP48E1
       generic map (
         -- Feature Control Attributes: Data Path Selection
         A_INPUT => "DIRECT",-- Selects A input source, "DIRECT" (A port) or "CASCADE" (ACIN port)
         B_INPUT => "DIRECT",-- Selects B input source, "DIRECT" (B port) or "CASCADE" (BCIN port)
         USE_DPORT => FALSE, -- Select D port usage (TRUE or FALSE)
         USE_MULT => "NONE", -- Select multiplier usage ("MULTIPLY", "DYNAMIC", or "NONE")
         -- Pattern Detector Attributes: Pattern Detection Configuration
         AUTORESET_PATDET => "NO_RESET",   -- "NO_RESET", "RESET_MATCH", "RESET_NOT_MATCH"
         MASK => X"3fffffffffff",          -- 48-bit mask value for pattern detect (1=ignore)
         PATTERN => X"000000000000",       -- 48-bit pattern match for pattern detect
         SEL_MASK => "MASK",               -- "C", "MASK", "ROUNDING_MODE1", "ROUNDING_MODE2"
         SEL_PATTERN => "PATTERN",         -- Select pattern value ("PATTERN" or "C")
         USE_PATTERN_DETECT => "NO_PATDET",-- Enable pattern detect ("PATDET" or "NO_PATDET")
         -- Register Control Attributes: Pipeline Register Configuration
         ACASCREG => REG_IN,    -- Number of pipeline stages between A/ACIN and ACOUT (0, 1 or 2)
         ADREG => 0,            -- Number of pipeline stages for pre-adder (0 or 1)
         ALUMODEREG => REG_IN,  -- Number of pipeline stages for ALUMODE (0 or 1)
         AREG => REG_IN,        -- Number of pipeline stages for A (0, 1 or 2)
         BCASCREG => REG_IN,    -- Number of pipeline stages between B/BCIN and BCOUT (0, 1 or 2)
         BREG => REG_IN,        -- Number of pipeline stages for B (0, 1 or 2)
         CARRYINREG => REG_IN,  -- Number of pipeline stages for CARRYIN (0 or 1)
         CARRYINSELREG => 0,    -- Number of pipeline stages for CARRYINSEL (0 or 1)
         CREG => REG_IN,        -- Number of pipeline stages for C (0 or 1)
         DREG => 0,             -- Number of pipeline stages for D (0 or 1)
         INMODEREG => 0,        -- Number of pipeline stages for INMODE (0 or 1)
         MREG => 0,             -- Number of multiplier pipeline stages (0 or 1)
         OPMODEREG => 1,        -- Number of pipeline stages for OPMODE (0 or 1)
         PREG => REG_OUT,       -- Number of pipeline stages for P (0 or 1)
         USE_SIMD => "ONE48"    -- SIMD selection ("ONE48", "TWO24", "FOUR12")
       ) port map (
        -- Cascade: 30-bit (each) output: Cascade Ports
         ACOUT => open,                -- 30-bit output: A port cascade output
         BCOUT => open,                -- 18-bit output: B port cascade output
         CARRYCASCOUT => out_cas_carry,-- 1-bit output: Cascade carry output
         MULTSIGNOUT => open,          -- 1-bit output: Multiplier sign cascade output
         PCOUT => open,                -- 48-bit output: Cascade output
         -- Control: 1-bit (each) output: Control Inputs/Status Bits
         OVERFLOW => open,             -- 1-bit output: Overflow in add/acc output
         PATTERNBDETECT => open,       -- 1-bit output: Pattern bar detect output
         PATTERNDETECT => open,        -- 1-bit output: Pattern detect output
         UNDERFLOW => open,            -- 1-bit output: Underflow in add/acc output
         -- Data: 4-bit (each) output: Data Ports
         CARRYOUT => out_carry,             -- 4-bit output: Carry output
         P => P,                       -- 48-bit output: Primary data output
         -- Cascade: 30-bit (each) input: Cascade Ports
         ACIN => zeros(29 downto 0),   -- 30-bit input: A cascade data input
         BCIN => zeros(17 downto 0),   -- 18-bit input: B cascade input
         CARRYCASCIN => carry_cas,     -- 1-bit input: Cascade carry input
         MULTSIGNIN => '1',            -- 1-bit input: Multiplier sign input
         PCIN => zeros(47 downto 0),   -- 48-bit input: P cascade input
         -- Control: 4-bit (each) input: Control Inputs/Status Bits
         ALUMODE => mode,              -- 4-bit input: ALU control input (X XOR Z)
         CARRYINSEL => carryinsel,     -- 3-bit input: Carry select input
         CEINMODE => '1',              -- 1-bit input: Clock enable input for INMODEREG
         CLK => CLK,                   -- 1-bit input: Clock input
         INMODE => "00000",            -- 5-bit input: INMODE control input
         OPMODE => op_mode,            -- 7-bit input: Operation mode input
         RSTINMODE => '0',             -- 1-bit input: Reset input for INMODEREG
         -- Data: 30-bit (each) input: Data Ports
         A => B(47 downto 18),         -- 30-bit input: A data input
         B => B(17 downto 0),          -- 18-bit input: B data input
         C => A,                       -- 48-bit input: C data input
         CARRYIN => carry,             -- 1-bit input: Carry input signal
         D => zeros(24 downto 0),      -- 25-bit input: D data input
         -- Reset/Clock Enable: 1-bit (each) input: Reset/Clock Enable Inputs
         CEA1 => CE_IN,         -- 1-bit input: Clock enable input for 1st stage AREG
         CEA2 => CE_IN,         -- 1-bit input: Clock enable input for 2nd stage AREG
         CEAD => '1',           -- 1-bit input: Clock enable input for ADREG
         CEALUMODE => CE_IN,    -- 1-bit input: Clock enable input for ALUMODERE
         CEB1 => CE_IN,         -- 1-bit input: Clock enable input for 1st stage BREG
         CEB2 => CE_IN,         -- 1-bit input: Clock enable input for 2nd stage BREG
         CEC => CE_IN,          -- 1-bit input: Clock enable input for CREG
         CECARRYIN => CE_IN,    -- 1-bit input: Clock enable input for CARRYINREG
         CECTRL => CE_IN,       -- 1-bit input: Clock enable input for OPMODEREG and CARRYINSELREG
         CED => '1',            -- 1-bit input: Clock enable input for DREG
         CEM => '1',            -- 1-bit input: Clock enable input for MREG
         CEP => CE_OUT,         -- 1-bit input: Clock enable input for PREG
         RSTA => RESET,         -- 1-bit input: Reset input for AREG
         RSTALLCARRYIN => RESET,-- 1-bit input: Reset input for CARRYINREG
         RSTALUMODE => RESET,   -- 1-bit input: Reset input for ALUMODEREG
         RSTB => RESET,         -- 1-bit input: Reset input for BREG
         RSTC => RESET,         -- 1-bit input: Reset input for CREG
         RSTCTRL => RESET,      -- 1-bit input: Reset input for OPMODEREG and CARRYINSELREG
         RSTD => RESET,         -- 1-bit input: Reset input for DREG and ADREG
         RSTM => RESET,         -- 1-bit input: Reset input for MREG
         RSTP => RESET          -- 1-bit input: Reset input for PREG
       );
   end generate;

   GEN_ALU_DSP2: if (REG_IN = 2) generate
       --! DSP slice instantion
       DSP48E1_inst : DSP48E1
       generic map (
         -- Feature Control Attributes: Data Path Selection
         A_INPUT => "DIRECT",-- Selects A input source, "DIRECT" (A port) or "CASCADE" (ACIN port)
         B_INPUT => "DIRECT",-- Selects B input source, "DIRECT" (B port) or "CASCADE" (BCIN port)
         USE_DPORT => FALSE, -- Select D port usage (TRUE or FALSE)
         USE_MULT => "NONE", -- Select multiplier usage ("MULTIPLY", "DYNAMIC", or "NONE")
         -- Pattern Detector Attributes: Pattern Detection Configuration
         AUTORESET_PATDET => "NO_RESET",   -- "NO_RESET", "RESET_MATCH", "RESET_NOT_MATCH"
         MASK => X"3fffffffffff",          -- 48-bit mask value for pattern detect (1=ignore)
         PATTERN => X"000000000000",       -- 48-bit pattern match for pattern detect
         SEL_MASK => "MASK",               -- "C", "MASK", "ROUNDING_MODE1", "ROUNDING_MODE2"
         SEL_PATTERN => "PATTERN",         -- Select pattern value ("PATTERN" or "C")
         USE_PATTERN_DETECT => "NO_PATDET",-- Enable pattern detect ("PATDET" or "NO_PATDET")
         -- Register Control Attributes: Pipeline Register Configuration
         ACASCREG => 1,    -- Number of pipeline stages between A/ACIN and ACOUT (0, 1 or 2)
         ADREG => 0,            -- Number of pipeline stages for pre-adder (0 or 1)
         ALUMODEREG => 1,  -- Number of pipeline stages for ALUMODE (0 or 1)
         AREG => 1,        -- Number of pipeline stages for A (0, 1 or 2)
         BCASCREG => 1,    -- Number of pipeline stages between B/BCIN and BCOUT (0, 1 or 2)
         BREG => 1,        -- Number of pipeline stages for B (0, 1 or 2)
         CARRYINREG => 0,  -- Number of pipeline stages for CARRYIN (0 or 1)
         CARRYINSELREG => 0,    -- Number of pipeline stages for CARRYINSEL (0 or 1)
         CREG => 1,        -- Number of pipeline stages for C (0 or 1)
         DREG => 0,             -- Number of pipeline stages for D (0 or 1)
         INMODEREG => 0,        -- Number of pipeline stages for INMODE (0 or 1)
         MREG => 0,             -- Number of multiplier pipeline stages (0 or 1)
         OPMODEREG => 1,   -- Number of pipeline stages for OPMODE (0 or 1)
         PREG => REG_OUT,       -- Number of pipeline stages for P (0 or 1)
         USE_SIMD => "ONE48"    -- SIMD selection ("ONE48", "TWO24", "FOUR12")
       ) port map (
        -- Cascade: 30-bit (each) output: Cascade Ports
         ACOUT => open,                -- 30-bit output: A port cascade output
         BCOUT => open,                -- 18-bit output: B port cascade output
         CARRYCASCOUT => out_cas_carry,-- 1-bit output: Cascade carry output
         MULTSIGNOUT => open,          -- 1-bit output: Multiplier sign cascade output
         PCOUT => open,                -- 48-bit output: Cascade output
         -- Control:   end generate;1-bit (each) output: Control Inputs/Status Bits
         OVERFLOW => open,             -- 1-bit output: Overflow in add/acc output
         PATTERNBDETECT => open,       -- 1-bit output: Pattern bar detect output
         PATTERNDETECT => open,        -- 1-bit output: Pattern detect output
         UNDERFLOW => open,            -- 1-bit output: Underflow in add/acc output
         -- Data: 4-bit (each) output: Data Ports
         CARRYOUT => out_carry,        -- 4-bit output: Carry output
         P => P,                       -- 48-bit output: Primary data output
         -- Cascade: 30-bit (each) input: Cascade Ports
         ACIN => zeros(29 downto 0),   -- 30-bit input: A cascade data input
         BCIN => zeros(17 downto 0),   -- 18-bit input: B cascade input
         CARRYCASCIN => '0',           -- 1-bit input: Cascade carry input
         MULTSIGNIN => '1',            -- 1-bit input: Multiplier sign input
         PCIN => zeros(47 downto 0),   -- 48-bit input: P cascade input
         -- Control: 4-bit (each) input: Control Inputs/Status Bits
         ALUMODE => mode,              -- 4-bit input: ALU control input (X XOR Z)
         CARRYINSEL => "000",          -- 3-bit input: Carry select input
         CEINMODE => '1',              -- 1-bit input: Clock enable input for INMODEREG
         CLK => CLK,                   -- 1-bit input: Clock input
         INMODE => "00000",            -- 5-bit input: INMODE control input
         OPMODE => op_mode,            -- 7-bit input: Operation mode input
         RSTINMODE => '0',             -- 1-bit input: Reset input for INMODEREG
         -- Data: 30-bit (each) input: Data Ports
         A => B(47 downto 18),         -- 30-bit input: A data input
         B => B(17 downto 0),          -- 18-bit input: B data input
         C => A,                       -- 48-bit input: C data input
         CARRYIN => CARRY_IN,          -- 1-bit input: Carry input signal
         D => zeros(24 downto 0),      -- 25-bit input: D data input
         -- Reset/Clock Enable: 1-bit (each) input: Reset/Clock Enable Inputs
         CEA1 => CE_IN,         -- 1-bit input: Clock enable input for 1st stage AREG
         CEA2 => CE_IN,         -- 1-bit input: Clock enable input for 2nd stage AREG
         CEAD => '1',           -- 1-bit input: Clock enable input for ADREG
         CEALUMODE => CE_IN,    -- 1-bit input: Clock enable input for ALUMODERE
         CEB1 => CE_IN,         -- 1-bit input: Clock enable input for 1st stage BREG
         CEB2 => CE_IN,         -- 1-bit input: Clock enable input for 2nd stage BREG
         CEC => CE_IN,          -- 1-bit input: Clock enable input for CREG
         CECARRYIN => CE_IN,    -- 1-bit input: Clock enable input for CARRYINREG
         CECTRL => CE_IN,       -- 1-bit input: Clock enable input for OPMODEREG and CARRYINSELREG
         CED => '1',            -- 1-bit input: Clock enable input for DREG
         CEM => '1',            -- 1-bit input: Clock enable input for MREG
         CEP => CE_OUT,         -- 1-bit input: Clock enable input for PREG
         RSTA => RESET,         -- 1-bit input: Reset input for AREG
         RSTALLCARRYIN => RESET,-- 1-bit input: Reset input for CARRYINREG
         RSTALUMODE => RESET,   -- 1-bit input: Reset input for ALUMODEREG
         RSTB => RESET,         -- 1-bit input: Reset input for BREG
         RSTC => RESET,         -- 1-bit input: Reset input for CREG
         RSTCTRL => RESET,      -- 1-bit input: Reset input for OPMODEREG and CARRYINSELREG
         RSTD => RESET,         -- 1-bit input: Reset input for DREG and ADREG
         RSTM => RESET,         -- 1-bit input: Reset input for MREG
         RSTP => RESET          -- 1-bit input: Reset input for PREG
       );
   end generate;
end V7_DSP;
