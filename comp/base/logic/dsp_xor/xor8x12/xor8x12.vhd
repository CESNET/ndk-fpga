-- xor8x12.vhd:  Implemented XOR function in DSP48E2 slice.
--             First half of 96-bit string is compared to the second half of the string.
-- Copyright (C) 2018 CESNET
-- Author(s)   Petr Panák <xpanak04@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
--use IEEE.std_logic_unsigned.all;
--use IEEE.std_logic_arith.all;
Library UNISIM;
use UNISIM.vcomponents.all;

entity xor8x12 is
   generic (
      --! Input pipeline registers
      IREG     : integer := 0;
      --! Output pipeline registers
      OREG     : integer := 0
   );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;
      --! Data input
      DI       : in  std_logic_vector(95 downto 0);
      --! Data output[1]
      DO_8x12  : out std_logic_vector(7 downto 0);	-- 8x12-bit xor
      --! Clock enable for input pipeline registers
      CEI      : in  std_logic;
      --! Clock enable for output pipeline registers
      CEO      : in  std_logic
   );
end entity;

--! Vitrex-7 Ultrascale+ architecture of XOR96
architecture VU_DSP of xor8x12 is
   signal ab, c : std_logic_vector(47 downto 0);
begin

   -- Inputs to DSP
   ab <= DI(95 downto 90) & DI(83 downto 78) & DI(71 downto 66) & DI(59 downto 54) & DI(47 downto 42) & DI(35 downto 30) & DI(23 downto 18) & DI(11 downto 6);
   c <= DI(89 downto 84) & DI(77 downto 72) & DI(65 downto 60) & DI(53 downto 48) & DI(41 downto 36) & DI(29 downto 24) & DI(17 downto 12) & DI(5 downto 0);

   -- DSP slice instantion --
   DSP48E2_inst : DSP48E2
   generic map (
      -- Feature Control Attributes: Data Path Selection
      AMULTSEL => "A",                    -- Selects A input to multiplier (A, AD)
      A_INPUT => "DIRECT",                -- Selects A input source, "DIRECT" (A port) or "CASCADE" (ACIN port)
      BMULTSEL => "B",                    -- Selects B input to multiplier (AD, B)
      B_INPUT => "DIRECT",                -- Selects B input source, "DIRECT" (B port) or "CASCADE" (BCIN port)
      PREADDINSEL => "A",                 -- Selects input to pre-adder (A, B)
      RND => X"000000000000",             -- Rounding Constant
      USE_MULT => "NONE",                 -- Select multiplier usage (DYNAMIC, MULTIPLY, NONE)
      USE_SIMD => "ONE48",                -- SIMD selection (FOUR12, ONE48, TWO24)
      USE_WIDEXOR => "TRUE",              -- Use the Wide XOR function (FALSE, TRUE)
      XORSIMD => "XOR12",           -- Mode of operation for the Wide XOR (XOR12, XOR24_48_96)
      -- Pattern Detector Attributes: Pattern Detection Configuration
      AUTORESET_PATDET => "NO_RESET",     -- NO_RESET, RESET_MATCH, RESET_NOT_MATCH
      AUTORESET_PRIORITY => "RESET",      -- Priority of AUTORESET vs. CEO (CEO, RESET).
      MASK => X"3fffffffffff",            -- 48-bit mask value for pattern detect (1=ignore)
      PATTERN => X"000000000000",         -- 48-bit pattern match for pattern detect
      SEL_MASK => "MASK",                 -- C, MASK, ROUNDING_MODE1, ROUNDING_MODE2
      SEL_PATTERN => "PATTERN",           -- Select pattern value (C, PATTERN)
      USE_PATTERN_DETECT => "NO_PATDET",  -- Enable pattern detect (NO_PATDET, PATDET)
      -- Programmable Inversion Attributes: Specifies built-in programmable inversion on specific pins
      IS_ALUMODE_INVERTED => "0000",      -- Optional inversion for ALUMODE
      IS_CARRYIN_INVERTED => '0',         -- Optional inversion for CARRYIN
      IS_CLK_INVERTED => '0',             -- Optional inversion for CLK
      IS_INMODE_INVERTED => "00000",      -- Optional inversion for INMODE
      IS_OPMODE_INVERTED => "000000000",  -- Optional inversion for OPMODE
      IS_RSTALLCARRYIN_INVERTED => '0',   -- Optional inversion for RSTALLCARRYIN
      IS_RSTALUMODE_INVERTED => '0',      -- Optional inversion for RSTALUMODE
      IS_RSTA_INVERTED => '0',            -- Optional inversion for RSTA
      IS_RSTB_INVERTED => '0',            -- Optional inversion for RSTB
      IS_RSTCTRL_INVERTED => '0',         -- Optional inversion for RSTCTRL
      IS_RSTC_INVERTED => '0',            -- Optional inversion for RSTC
      IS_RSTD_INVERTED => '0',            -- Optional inversion for RSTD
      IS_RSTINMODE_INVERTED => '0',       -- Optional inversion for RSTINMODE
      IS_RSTM_INVERTED => '0',            -- Optional inversion for RSTM
      IS_RSTP_INVERTED => '0',            -- Optional inversion for RSTP
      -- Register Control Attributes: Pipeline Register Configuration
      ACASCREG => IREG,                   -- Number of pipeline stages between A/ACIN and ACOUT (0-2)
      ADREG => 0,                         -- Pipeline stages for pre-adder (0-1)
      ALUMODEREG => 0,                    -- Pipeline stages for ALUMODE (0-1)
      AREG => IREG,                       -- Pipeline stages for A (0-2)
      BCASCREG => IREG,                   -- Number of pipeline stages between B/BCIN and BCOUT (0-2)
      BREG => IREG,                       -- Pipeline stages for B (0-2)
      CARRYINREG => 0,                    -- Pipeline stages for CARRYIN (0-1)
      CARRYINSELREG => 0,                 -- Pipeline stages for CARRYINSEL (0-1)
      CREG => IREG,                       -- Pipeline stages for C (0-1)
      DREG => 0,                          -- Pipeline stages for D (0-1)
      INMODEREG => 0,                     -- Pipeline stages for INMODE (0-1)
      MREG => 0,                          -- Multiplier pipeline stages (0-1)
      OPMODEREG => 0,                     -- Pipeline stages for OPMODE (0-1)
      PREG => OREG                        -- Number of pipeline stages for P (0-1)
   )
   port map (
      -- Cascade outputs: Cascade Ports
      ACOUT => open,                   -- 30-bit output: A port cascade
      BCOUT => open,                   -- 18-bit output: B cascade
      CARRYCASCOUT => open,            -- 1-bit output: Cascade carry
      MULTSIGNOUT => open,             -- 1-bit output: Multiplier sign cascade
      PCOUT => open,                   -- 48-bit output: Cascade output
      -- Control outputs: Control Inputs/Status Bits
      OVERFLOW => open,                -- 1-bit output: Overflow in add/acc
      PATTERNBDETECT => open,          -- 1-bit output: Pattern bar detect
      PATTERNDETECT => open,           -- 1-bit output: Pattern detect
      UNDERFLOW => open,               -- 1-bit output: Underflow in add/acc
      -- Data outputs: Data Ports
      CARRYOUT => open,                -- 4-bit output: Carry
      P => open,                       -- 48-bit output: Primary data
      XOROUT => DO_8x12,               -- 8-bit output: XOR data
      -- Cascade inputs: Cascade Ports
      ACIN => (29 downto 0 => '0'),    -- 30-bit input: A cascade data
      BCIN => (17 downto 0 => '0'),    -- 18-bit input: B cascade
      CARRYCASCIN => '0',              -- 1-bit input: Cascade carry
      MULTSIGNIN => '0',               -- 1-bit input: Multiplier sign cascade
      PCIN => (others => '0'),         -- 48-bit input: P cascade
      -- Control inputs: Control Inputs/Status Bits
      ALUMODE => "0100",               -- 4-bit input: ALU control
      CARRYINSEL => "000",             -- 3-bit input: Carry select
      CLK => CLK,                      -- 1-bit input: Clock
      INMODE => "00000",               -- 5-bit input: INMODE control
      OPMODE => "000110011",           -- 9-bit input: Operation mode
      -- Data inputs: Data Ports
      A => ab(47 downto 18),           -- 30-bit input: A data
      B => ab(17 downto 0),            -- 18-bit input: B data
      C => c, 			       -- 48-bit input: C data
      CARRYIN => '0',                  -- 1-bit input: Carry-in
      D => (26 downto 0 => '0'),       -- 27-bit input: D data
      -- Reset/Clock Enable inputs: Reset/Clock Enable Inputs
      CEA1 => CEI,                     -- 1-bit input: Clock enable for 1st stage AREG
      CEA2 => CEI,                     -- 1-bit input: Clock enable for 2nd stage AREG
      CEAD => '0',                     -- 1-bit input: Clock enable for ADREG
      CEALUMODE => '1',                -- 1-bit input: Clock enable for ALUMODE
      CEB1 => CEI,                     -- 1-bit input: Clock enable for 1st stage BREG
      CEB2 => CEI,                     -- 1-bit input: Clock enable for 2nd stage BREG
      CEC => CEI,                      -- 1-bit input: Clock enable for IREG
      CECARRYIN => '0',                -- 1-bit input: Clock enable for CARRYINREG
      CECTRL => '1',                   -- 1-bit input: Clock enable for OPMODEREG and CARRYINSELREG
      CED => '0',                      -- 1-bit input: Clock enable for DREG
      CEINMODE => CEI,                 -- 1-bit input: Clock enable for INMODEREG
      CEM => '1',                      -- 1-bit input: Clock enable for MREG
      CEP => CEO,                      -- 1-bit input: Clock enable for OREG
      RSTA => RESET,                   -- 1-bit input: Reset for AREG
      RSTALLCARRYIN => RESET,          -- 1-bit input: Reset for CARRYINREG
      RSTALUMODE => RESET,             -- 1-bit input: Reset for ALUMODEREG
      RSTB => RESET,                   -- 1-bit input: Reset for BREG
      RSTC => RESET,                   -- 1-bit input: Reset for IREG
      RSTCTRL => RESET,                -- 1-bit input: Reset for OPMODEREG and CARRYINSELREG
      RSTD => RESET,                   -- 1-bit input: Reset for DREG and ADREG
      RSTINMODE => RESET,              -- 1-bit input: Reset for INMODEREG
      RSTM => RESET,                   -- 1-bit input: Reset for MREG
      RSTP => RESET                    -- 1-bit input: Reset for OREG
   );

end architecture;
