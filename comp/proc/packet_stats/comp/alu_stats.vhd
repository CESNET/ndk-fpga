--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2016
--!
--! \section License
--!
--! Copyright (C) 2016 CESNET
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
entity ALU_STATS is
   generic (
      EN_DSP   : boolean := true;
      --! Width max 48 bits
      A_WIDTH  : integer := 48;
      B_WIDTH  : integer := 16;
      P_WIDTH  : integer := 48;
      REG_OUT  : integer := 0
   );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;
      --! Enable adder
      EN_ADD   : in std_logic;
      --! Reset adder
      RST_ADD  : in std_logic;
      --! Data input
      A        : in  std_logic_vector(A_WIDTH-1 downto 0);
      --! Data input
      B        : in  std_logic_vector(B_WIDTH-1 downto 0);
      --! Latency = 0 + REG_OUT
      P        : out std_logic_vector(P_WIDTH-1 downto 0)
     );
end entity;

--! Vitrex-7 architecture of ALU48
architecture FULL of ALU_STATS is
   --! signals
   signal zeros      : std_logic_vector(63 downto 0);
begin
   zeros <= X"0000000000000000";

   gen_dps : if(EN_DSP = true) generate
      signal in_a    : std_logic_vector(47 downto 0);
      signal in_b    : std_logic_vector(47 downto 0);
      signal out_p   : std_logic_vector(47 downto 0);
      signal en_B    : std_logic;
      signal en_A    : std_logic;
      signal opmode  : std_logic_vector(6 downto 0);
   begin

      in_a(A_WIDTH-1 downto 0) <= A;
      in_a(47 downto A_WIDTH) <= (others => '0');
      in_b(B_WIDTH-1 downto 0) <= B;
      in_b(47 downto B_WIDTH) <= (others => '0');
      P <= out_p(P_WIDTH-1 downto 0);

      -- enable B in
      en_B <= '0' when RST_ADD = '1' else
              '1' when EN_ADD = '1' else
              '0';
      -- enable A in
      en_A <= '0' when RST_ADD = '1' else
              '1';

      opmode <= '0' & en_A & en_A & "00" & en_B & en_B;

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
        ACASCREG => 0,         -- Number of pipeline stages between A/ACIN and ACOUT (0, 1 or 2)
        ADREG => 0,            -- Number of pipeline stages for pre-adder (0 or 1)
        ALUMODEREG => 0,       -- Number of pipeline stages for ALUMODE (0 or 1)
        AREG => 0,             -- Number of pipeline stages for A (0, 1 or 2)
        BCASCREG => 0,         -- Number of pipeline stages between B/BCIN and BCOUT (0, 1 or 2)
        BREG => 0,             -- Number of pipeline stages for B (0, 1 or 2)
        CARRYINREG => 0,       -- Number of pipeline stages for CARRYIN (0 or 1)
        CARRYINSELREG => 0,    -- Number of pipeline stages for CARRYINSEL (0 or 1)
        CREG => 0,             -- Number of pipeline stages for C (0 or 1)
        DREG => 0,             -- Number of pipeline stages for D (0 or 1)
        INMODEREG => 0,        -- Number of pipeline stages for INMODE (0 or 1)
        MREG => 0,             -- Number of multiplier pipeline stages (0 or 1)
        OPMODEREG => 0,        -- Number of pipeline stages for OPMODE (0 or 1)
        PREG => REG_OUT,       -- Number of pipeline stages for P (0 or 1)
        USE_SIMD => "ONE48"    -- SIMD selection ("ONE48", "TWO24", "FOUR12")
      ) port map (
       -- Cascade: 30-bit (each) output: Cascade Ports
        ACOUT => open,                -- 30-bit output: A port cascade output
        BCOUT => open,                -- 18-bit output: B port cascade output
        CARRYCASCOUT => open,         -- 1-bit output: Cascade carry output
        MULTSIGNOUT => open,          -- 1-bit output: Multiplier sign cascade output
        PCOUT => open,                -- 48-bit output: Cascade output
        -- Control: 1-bit (each) output: Control Inputs/Status Bits
        OVERFLOW => open,             -- 1-bit output: Overflow in add/acc output
        PATTERNBDETECT => open,       -- 1-bit output: Pattern bar detect output
        PATTERNDETECT => open,        -- 1-bit output: Pattern detect output
        UNDERFLOW => open,            -- 1-bit output: Underflow in add/acc output
        -- Data: 4-bit (each) output: Data Ports
        CARRYOUT => open,             -- 4-bit output: Carry output
        P => out_p,                   -- 48-bit output: Primary data output
        -- Cascade: 30-bit (each) input: Cascade Ports
        ACIN => zeros(29 downto 0),   -- 30-bit input: A cascade data input
        BCIN => zeros(17 downto 0),   -- 18-bit input: B cascade input
        CARRYCASCIN => '0',           -- 1-bit input: Cascade carry input
        MULTSIGNIN => '1',            -- 1-bit input: Multiplier sign input
        PCIN => zeros(47 downto 0),   -- 48-bit input: P cascade input
        -- Control: 4-bit (each) input: Control Inputs/Status Bits
        ALUMODE => "0000",            -- 4-bit input: ALU control input (X XOR Z)
        CARRYINSEL => (others => '0'),-- 3-bit input: Carry select input
        CEINMODE => '1',              -- 1-bit input: Clock enable input for INMODEREG
        CLK => CLK,                   -- 1-bit input: Clock input
        INMODE => "00000",            -- 5-bit input: INMODE control input
        OPMODE => opmode,             -- 7-bit input: Operation mode input
        RSTINMODE => '0',             -- 1-bit input: Reset input for INMODEREG
        -- Data: 30-bit (each) input: Data Ports
        A => in_b(47 downto 18),      -- 30-bit input: A data input
        B => in_b(17 downto 0),       -- 18-bit input: B data input
        C => in_a,                    -- 48-bit input: C data input
        CARRYIN => '0',               -- 1-bit input: Carry input signal
        D => zeros(24 downto 0),      -- 25-bit input: D data input
        -- Reset/Clock Enable: 1-bit (each) input: Reset/Clock Enable Inputs
        CEA1 => '1',           -- 1-bit input: Clock enable input for 1st stage AREG
        CEA2 => '1',           -- 1-bit input: Clock enable input for 2nd stage AREG
        CEAD => '1',           -- 1-bit input: Clock enable input for ADREG
        CEALUMODE => '1',      -- 1-bit input: Clock enable input for ALUMODERE
        CEB1 => '1',           -- 1-bit input: Clock enable input for 1st stage BREG
        CEB2 => '1',           -- 1-bit input: Clock enable input for 2nd stage BREG
        CEC => '1',            -- 1-bit input: Clock enable input for CREG
        CECARRYIN => '1',      -- 1-bit input: Clock enable input for CARRYINREG
        CECTRL => '1',         -- 1-bit input: Clock enable input for OPMODEREG and CARRYINSELREG
        CED => '1',            -- 1-bit input: Clock enable input for DREG
        CEM => '1',            -- 1-bit input: Clock enable input for MREG
        CEP => '1',            -- 1-bit input: Clock enable input for PREG
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


   BEH_ALU : if(EN_DSP = false) generate
      signal in_a  : std_logic_vector(A'range);
      signal in_b  : std_logic_vector(B'range);
      signal out_p : std_logic_vector(P'range);
   begin

      in_b <= (others => '0') when RST_ADD = '1' else
              B               when EN_ADD = '1' else
              (others => '0');

      in_a <= (others => '0') when RST_ADD = '1' else
              A;

      out_p <= in_a + in_b;

      GEN_REG_on : if(REG_OUT = 1) generate
         process(CLK)
         begin
            if (CLK'event) and (CLK = '1') then
               if (RESET = '1') then
                  P <= (others => '0');
               else
                  P <= out_p;
               end if;
            end if;
         end process;
      end generate;

      GEN_REG_off : if(REG_OUT = 0) generate
         P <= out_p;
      end generate;

   end generate;
end architecture;
