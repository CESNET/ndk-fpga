--! count48.vhd
--!
--! \file
--! \brief counter  implemented with Virtex-7 DSP slice
--! Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2013
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

--! \brief DSP slice COUNTER entity
entity COUNT48 is
   generic (
      --! Input pipeline registers (0, 1)
      REG_IN      : integer := 1;
      --! "NO_RESET", "RESET_MATCH", "RESET_NOT_MATCH"
      AUTO_RESET  : string  := "NO_RESET";
      --! selecnt nosrmal or cascade(0/1) carryin
      CARRY_SEL   : integer := 1;
      DEVICE      : string  := "7SERIES"
     );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Enable input
      ENABLE   : in std_logic;
      ENABLE_IN: in std_logic;
      --! Reset input
      RESET         : in  std_logic;
      RESET_OUT     : in  std_logic;
      --! casrryin for cascade
      CAS_CARRY_IN  : in  std_logic;
      --! Data input
      A        : in  std_logic_vector(47 downto 0);
      --! Data input (must MAX % A = 0)
      MAX      : in  std_logic_vector(47 downto 0);
      --! Data output
      P        : out std_logic_vector(47 downto 0);
      --! carryout for cascade
      CAS_CARRY_OUT : out std_logic;
      --! indicate pattern
      PATTERN : out std_logic
   );
end COUNT48;

--! Vitrex-7 architecture of COUNT48
architecture V7_DSP of COUNT48 is

   constant DEVICE_HAS_DSP48E : boolean := DEVICE = "7SERIES" or DEVICE = "ULTRASCALE";

   --! signals
   signal zeros    : std_logic_vector(63 downto 0);
   signal enable_p : std_logic;
   --! select carry in
   signal carry_in_sel : std_logic_vector(2 downto 0);

begin
   gen_normal_carry_in : if (CARRY_SEL = 0) generate
      carry_in_sel <= "000";
   end generate;

   gen_cascade_carry_in : if (CARRY_SEL = 1) generate
      carry_in_sel <= "010";
   end generate;

   zeros <= X"0000000000000000";

   reg_of : if (REG_IN = 0 OR REG_IN = 3) generate
      enable_p <= ENABLE;
   end generate;

   reg_on : if (REG_IN = 1) generate
      process(CLK)
      begin
         if (CLK'event) and (CLK='1') then
            if (RESET='1') then
               enable_p <= '0';
            else
               enable_p <= ENABLE;
            end if;
         end if;
      end process;
   end generate;

dsp48e_g: if DEVICE_HAS_DSP48E generate
   --! DSP slice instantion
   DSP48E1_inst : DSP48E1
   generic map (
      -- Feature Control Attributes: Data Path Selection
      A_INPUT => "DIRECT",-- Selects A input source, "DIRECT" (A port) or "CASCADE" (ACIN port)
      B_INPUT => "DIRECT",-- Selects B input source, "DIRECT" (B port) or "CASCADE" (BCIN port)
      USE_DPORT => FALSE, -- Select D port usage (TRUE or FALSE)
      USE_MULT => "NONE", -- Select multiplier usage ("MULTIPLY", "DYNAMIC", or "NONE")
      -- Pattern Detector Attributes: Pattern Detection Configuration
      AUTORESET_PATDET => AUTO_RESET,  -- "NO_RESET", "RESET_MATCH", "RESET_NOT_MATCH"
      MASK => X"000000000000",         -- 48-bit mask value for pattern detect (1=ignore)
      PATTERN => X"000000000000",      -- 48-bit pattern match for pattern detect
      SEL_MASK => "MASK",              -- "C", "MASK", "ROUNDING_MODE1", "ROUNDING_MODE2"
      SEL_PATTERN => "C",              -- Select pattern value ("PATTERN" or "C")
      USE_PATTERN_DETECT => "PATDET",  -- Enable pattern detect ("PATDET" or "NO_PATDET")
      -- Register Control Attributes: Pipeline Register Configuration
      ACASCREG => REG_IN mod 2,    -- Number of pipeline stages between A/ACIN and ACOUT (0, 1 or 2)
      ADREG => 0,                -- Number of pipeline stages for pre-adder (0 or 1)
      ALUMODEREG => 0,           -- Number of pipeline stages for ALUMODE (0 or 1)
      AREG => REG_IN mod 2,        -- Number of pipeline stages for A (0, 1 or 2)
      BCASCREG => REG_IN mod 2,    -- Number of pipeline stages between B/BCIN and BCOUT (0, 1 or 2)
      BREG => REG_IN mod 2,        -- Number of pipeline stages for B (0, 1 or 2)
      CARRYINREG => 0,       -- Number of pipeline stages for CARRYIN (0 or 1)
      CARRYINSELREG => 0,    -- Number of pipeline stages for CARRYINSEL (0 or 1)
      CREG => REG_IN mod 2,  -- Number of pipeline stages for C (0 or 1)
      DREG => 0,             -- Number of pipeline stages for D (0 or 1)
      INMODEREG => 0,        -- Number of pipeline stages for INMODE (0 or 1)
      MREG => 0,             -- Number of multiplier pipeline stages (0 or 1)
      OPMODEREG => 1,        -- Number of pipeline stages for OPMODE (0 or 1)
      PREG => 1,             -- Number of pipeline stages for P (0 or 1)
      USE_SIMD => "ONE48"    -- SIMD selection ("ONE48", "TWO24", "FOUR12")
   ) port map (
      -- Cascade: 30-bit (each) output: Cascade Ports
      ACOUT => open,                -- 30-bit output: A port cascade output
      BCOUT => open,                -- 18-bit output: B port cascade output
      CARRYCASCOUT => CAS_CARRY_OUT,-- 1-bit output: Cascade carry output
      MULTSIGNOUT => open,          -- 1-bit output: Multiplier sign cascade output
      PCOUT => open,                -- 48-bit output: Cascade output
      -- Control: 1-bit (each) output: Control Inputs/Status Bits
      OVERFLOW => open,             -- 1-bit output: Overflow in add/acc output
      PATTERNBDETECT => open,       -- 1-bit output: Pattern bar detect output
      PATTERNDETECT => PATTERN,     -- 1-bit output: Pattern detect output
      UNDERFLOW => open,            -- 1-bit output: Underflow in add/acc output
      -- Data: 4-bit (each) output: Data Ports
      CARRYOUT => open,             -- 4-bit output: Carry output
      P => P,                       -- 48-bit output: Primary data output
      -- Cascade: 30-bit (each) input: Cascade Ports
      ACIN => zeros(29 downto 0),   -- 30-bit input: A cascade data input
      BCIN => zeros(17 downto 0),   -- 18-bit input: B cascade input
      CARRYCASCIN => CAS_CARRY_IN,  -- 1-bit input: Cascade carry input
      MULTSIGNIN => '0',            -- 1-bit input: Multiplier sign input
      PCIN => zeros(47 downto 0),   -- 48-bit input: P cascade input
      -- Control: 4-bit (each) input: Control Inputs/Status Bits
      ALUMODE => "0000",            -- 4-bit input: ALU control input (X XOR Z)
      CARRYINSEL => carry_in_sel,   -- 3-bit input: Carry select input
      CEINMODE => '1',              -- 1-bit input: Clock enable input for INMODEREG
      CLK => CLK,                   -- 1-bit input: Clock input
      INMODE => "00000",            -- 5-bit input: INMODE control input
      OPMODE => "0100011",          -- 7-bit input: Operation mode input
      RSTINMODE => '0',             -- 1-bit input: Reset input for INMODEREG
      -- Data: 30-bit (each) input: Data Ports
      A => A(47 downto 18),         -- 30-bit input: A data input
      B => A(17 downto 0),          -- 18-bit input: B data input
      C => MAX,                     -- 48-bit input: C data input
      CARRYIN => '0',               -- 1-bit input: Carry input signal
      D => zeros(24 downto 0),      -- 25-bit input: D data input
      -- Reset/Clock Enable: 1-bit (each) input: Reset/Clock Enable Inputs
      CEA1 => ENABLE_IN,   -- 1-bit input: Clock enable input for 1st stage AREG
      CEA2 => ENABLE_IN,   -- 1-bit input: Clock enable input for 2nd stage AREG
      CEAD => '1',         -- 1-bit input: Clock enable input for ADREG
      CEALUMODE => '1',    -- 1-bit input: Clock enable input for ALUMODERE
      CEB1 => ENABLE_IN,   -- 1-bit input: Clock enable input for 1st stage BREG
      CEB2 => ENABLE_IN,   -- 1-bit input: Clock enable input for 2nd stage BREG
      CEC => ENABLE_IN,    -- 1-bit input: Clock enable input for CREG
      CECARRYIN => '1',    -- 1-bit input: Clock enable input for CARRYINREG
      CECTRL => '1',       -- 1-bit input: Clock enable input for OPMODEREG and CARRYINSELREG
      CED => '1',          -- 1-bit input: Clock enable input for DREG
      CEM => '1',          -- 1-bit input: Clock enable input for MREG
      CEP => enable_p,     -- 1-bit input: Clock enable input for PREG
      RSTA => RESET,       -- 1-bit input: Reset input for AREG
      RSTALLCARRYIN => '0',-- 1-bit input: Reset input for CARRYINREG
      RSTALUMODE => '0',   -- 1-bit input: Reset input for ALUMODEREG
      RSTB => RESET,       -- 1-bit input: Reset input for BREG
      RSTC => RESET,       -- 1-bit input: Reset input for CREG
      RSTCTRL => '0',      -- 1-bit input: Reset input for OPMODEREG and CARRYINSELREG
      RSTD => '0',         -- 1-bit input: Reset input for DREG and ADREG
      RSTM => '0',         -- 1-bit input: Reset input for MREG
      RSTP => RESET_OUT    -- 1-bit input: Reset input for PREG
   );
end generate;
end V7_DSP;
