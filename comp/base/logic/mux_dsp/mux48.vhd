--! mux48.vhd
--!
--! \file
--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2015
--!
--! \section License
--! Copyright (C) 2014 CESNET
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
Library UNISIM;
use UNISIM.vcomponents.all;

--! \brief DSP slice ALU entity
entity MUX48 is
   generic (
      --! Input pipeline registers (0, 1)
      REG_IN_A    : integer := 0;
      REG_IN_B    : integer := 0;
      REG_SEL     : integer := 0;
      --! Output pipeline register (0, 1)
      REG_OUT     : integer := 0;
      --! enbale cascade on port B
      CASCADE_EN  : boolean := false;
      NEG_SEL     : boolean := false
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
      CE_IN_A  : in  std_logic;
      CE_IN_B  : in  std_logic;
      CE_SEL   : in  std_logic;
      --! SEL A OR B
      SEL      : in std_logic;
      --! Clock enable for output pipeline registers
      CE_OUT   : in  std_logic;
      --! output
      P        : out std_logic_vector(47 downto 0);
      P_CAS    : out std_logic_vector(47 downto 0)
   );
end entity;

architecture FULL of MUX48 is
   --! signals
   signal opmode  : std_logic_vector(6 downto 0);
   signal zeros   : std_logic_vector(63 downto 0);
   signal tmp_C   : std_logic_vector(47 downto 0);
   signal tmp_PCIN   : std_logic_vector(47 downto 0);
begin

   zeros <= X"0000000000000000";

   GEN_CASCADE_OFF: if(CASCADE_EN = false) generate
      NEG_SEL_OFF: if(NEG_SEL = false) generate
         opmode   <= (0 => not SEL, 1 => not SEL, 4 => SEL, 5 => SEL, others => '0');
      end generate;

      NEG_SEL_ON: if(NEG_SEL = true) generate
         opmode   <= (0 => SEL, 1 => SEL, 4 => not SEL, 5 => not SEL, others => '0');
      end generate;

      tmp_C    <= B;
      tmp_PCIN <= (others => '0');
   end generate;

   GEN_CASCADE_ON: if(CASCADE_EN = true) generate
      NEG_SEL_OFF: if(NEG_SEL = false) generate
         opmode   <= (0 => not SEL, 1 => not SEL, 4 => SEL, others => '0');
      end generate;

      NEG_SEL_ON: if(NEG_SEL = true) generate
         opmode   <= (0 => SEL, 1 => SEL, 4 => not SEL, others => '0');
      end generate;

      tmp_C    <= (others => '0');
      tmp_PCIN <= B;
   end generate;

   --! DSP slice instantion
   DSP48E1_inst : DSP48E1
   generic map (
      -- Feature Control Attributes: Data Path Selection
      A_INPUT => "DIRECT",   -- Selects A input source, "DIRECT" (A port) or "CASCADE" (ACIN port)
      B_INPUT => "DIRECT",   -- Selects B input source, "DIRECT" (B port) or "CASCADE" (BCIN port)
      USE_DPORT => FALSE,    -- Select D port usage (TRUE or FALSE)
      USE_MULT => "NONE",    -- Select multiplier usage ("MULTIPLY", "DYNAMIC", or "NONE")
      -- Pattern Detector Attributes: Pattern Detection Configuration
      AUTORESET_PATDET => "NO_RESET",  -- "NO_RESET", "RESET_MATCH", "RESET_NOT_MATCH"
      MASK => X"000000000000",         -- 48-bit mask value for pattern detect (1=ignore)
      PATTERN => X"000000000000",      -- 48-bit pattern match for pattern detect
      SEL_MASK => "MASK",              -- "C", "MASK", "ROUNDING_MODE1", "ROUNDING_MODE2"
      SEL_PATTERN => "PATTERN",           -- Select pattern value ("PATTERN" or "C")
      USE_PATTERN_DETECT => "NO_PATDET",  -- Enable pattern detect ("PATDET" or "NO_PATDET")
      -- Register Control Attributes: Pipeline Register Configuration
      ACASCREG => REG_IN_A,         -- Number of pipeline stages between A/ACIN and ACOUT (0, 1 or 2)
      ADREG => 0,                   -- Number of pipeline stages for pre-adder (0 or 1)
      ALUMODEREG => 0,              -- Number of pipeline stages for ALUMODE (0 or 1)
      AREG => REG_IN_A,             -- Number of pipeline stages for A (0, 1 or 2)
      BCASCREG => REG_IN_A,         -- Number of pipeline stages between B/BCIN and BCOUT (0, 1 or 2)
      BREG => REG_IN_A,             -- Number of pipeline stages for B (0, 1 or 2)
      CARRYINREG => 0,              -- Number of pipeline stages for CARRYIN (0 or 1)
      CARRYINSELREG => 0,           -- Number of pipeline stages for CARRYINSEL (0 or 1)
      CREG => REG_IN_B,             -- Number of pipeline stages for C (0 or 1)
      DREG => 0,                    -- Number of pipeline stages for D (0 or 1)
      INMODEREG => 0,               -- Number of pipeline stages for INMODE (0 or 1)
      MREG => 0,                    -- Number of multiplier pipeline stages (0 or 1)
      OPMODEREG => REG_SEL,               -- Number of pipeline stages for OPMODE (0 or 1)
      PREG => REG_OUT,              -- Number of pipeline stages for P (0 or 1)
      USE_SIMD => "ONE48"           -- SIMD selection ("ONE48", "TWO24", "FOUR12")
   ) port map (
      -- Cascade: 30-bit (each) output: Cascade Ports
      ACOUT => open,                -- 30-bit output: A port cascade output
      BCOUT => open,                -- 18-bit output: B port cascade output
      CARRYCASCOUT => open,         -- 1-bit output: Cascade carry output
      MULTSIGNOUT => open,          -- 1-bit output: Multiplier sign cascade output
      PCOUT => P_CAS,               -- 48-bit output: Cascade output
      -- Control: 1-bit (each) output: Control Inputs/Status Bits
      OVERFLOW => open,             -- 1-bit output: Overflow in add/acc output
      PATTERNBDETECT => open,       -- 1-bit output: Pattern bar detect output
      PATTERNDETECT => open,        -- 1-bit output: Pattern detect output
      UNDERFLOW => open,            -- 1-bit output: Underflow in add/acc output
      -- Data: 4-bit (each) output: Data Ports
      CARRYOUT => open,             -- 4-bit output: Carry output
      P => P,                    -- 48-bit output: Primary data output
      -- Cascade: 30-bit (each) input: Cascade Ports
      ACIN => zeros(29 downto 0),   -- 30-bit input: A cascade data input
      BCIN => zeros(17 downto 0),   -- 18-bit input: B cascade input
      CARRYCASCIN => '0',           -- 1-bit input: Cascade carry input
      MULTSIGNIN => '0',            -- 1-bit input: Multiplier sign input
      PCIN => tmp_PCIN,             -- 48-bit input: P cascade input
      -- Control: 4-bit (each) input: Control Inputs/Status Bits
      ALUMODE => "0000",            -- 4-bit input: ALU control input (X XOR Z)
      CARRYINSEL => "000",          -- 3-bit input: Carry select input
      CEINMODE => '1',              -- 1-bit input: Clock enable input for INMODEREG
      CLK => CLK,                   -- 1-bit input: Clock input
      INMODE => "00000",            -- 5-bit input: INMODE control input
      OPMODE => opmode,             -- 7-bit input: Operation mode input
      RSTINMODE => '0',             -- 1-bit input: Reset input for INMODEREG
      -- Data: 30-bit (each) input: Data Ports
      A => A(47 downto 18),      -- 30-bit input: A data input
      B => A(17 downto 0),       -- 18-bit input: B data input
      C => tmp_C,                -- 48-bit input: C data input
      CARRYIN => '0',            -- 1-bit input: Carry input signal
      D => zeros(24 downto 0),   -- 25-bit input: D data input
      -- Reset/Clock Enable: 1-bit (each) input: Reset/Clock Enable Inputs
      CEA1 => CE_IN_A,           -- 1-bit input: Clock enable input for 1st stage AREG
      CEA2 => CE_IN_A,           -- 1-bit input: Clock enable input for 2nd stage AREG
      CEAD => '1',               -- 1-bit input: Clock enable input for ADREG
      CEALUMODE => '1',          -- 1-bit input: Clock enable input for ALUMODERE
      CEB1 => CE_IN_A,           -- 1-bit input: Clock enable input for 1st stage BREG
      CEB2 => CE_IN_A,           -- 1-bit input: Clock enable input for 2nd stage BREG
      CEC => CE_IN_B,            -- 1-bit input: Clocik enable input for CREG
      CECARRYIN => '1',      -- 1-bit input: Clock enable input for CARRYINREG
      CECTRL => CE_SEL,      -- 1-bit input: Clock enable input for OPMODEREG and CARRYINSELREG
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
end architecture;
