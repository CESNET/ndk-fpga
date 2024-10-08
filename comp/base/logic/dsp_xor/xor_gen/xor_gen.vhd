-- generate.vhd: Implemented XOR function in DSP48E2 slice.
--             	First half of 384-bit string is xored with second half of the string.
-- Copyright (C) 2018 CESNET
-- Author(s) Petr Panak <xpanak04@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

-- [1] Explanation of component function with 384-bit input string. When 384-bit string is inputed,
-- it is splited into two parts (383 downto 192) and (191 downto 0). These two parts are xored with
-- each other.
-- Output DO_1 is result of xoring these two parts of the string.
-- Output DO_2 is result of xoring first half and second half of the splited signal. Then:
--    DO_2(1) is output for (383 downto 288) xored with (191 downto 96).
--    DO_2(0) is output for (287 downto 192) xored with (95 dowtno 0).
-- Output DO_4 is the same as DO_2 but both halfs of the string are splited into quarters.

library IEEE;
use IEEE.std_logic_1164.all;
--use IEEE.std_logic_unsigned.all;
--use IEEE.std_logic_arith.all;
Library UNISIM;
use UNISIM.vcomponents.all;

entity xor_gen is
   generic (
      --! Data width (96, 192, 288, 384, 576, 768 bits)
      DATA_WIDTH  : integer := 384;
      --! Input pipeline registers
      IREG        : integer := 0;
      --! Output popeline registers
      OREG        : integer := 0
   );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;
      --! Data input
      DI       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Data output[1]
      DO_1     : out std_logic;                    -- for whole string
      DO_2     : out std_logic_vector(1 downto 0); -- every bit for one half of the string
      DO_4     : out std_logic_vector(3 downto 0); -- every bit for one quarter of the string
      --! Clock enable for input pipeline registers
      CEI      : in  std_logic;
      --! Clock enable for output pipeline registers
      CEO      : in  std_logic
  );
end entity;

architecture VU_DSP of xor_gen is

   -- Output signal
   signal xorout : std_logic_vector(7 downto 0);
   -- Cascading signal (example: 4 DSP = 3x48-bit cascade)
   signal casc : std_logic_vector(DATA_WIDTH/2-1-48 downto 0);
   -- Signal array for data distribution
   type d_a is array (0 to DATA_WIDTH/96-1) of std_logic_vector(95 downto 0);
   signal d : d_a;
   -- Number of DSP blocks
   constant c_dsp : integer := DATA_WIDTH/96;

begin

   -- Generation of XOR component from DSP based on DATA_WIDTH --
   GEN_XOR: for I in 0 to c_dsp-1 generate
   begin

   -- Distribution of DI to DSP --
      GEN_sig: for J in 0 to 3 generate
      begin
         d(I)(96-1-J*12 downto 96-(J+1)*12) <= DI(DATA_WIDTH-1-I*12-J*c_dsp*12 downto DATA_WIDTH-(I+1)*12-J*c_dsp*12);
         d(I)(96/2-1-J*12 downto 96/2-(J+1)*12) <= DI(DATA_WIDTH/2-1-I*12-J*c_dsp*12 downto DATA_WIDTH/2-(I+1)*12-J*c_dsp*12);
      end generate;

      -- Generating one DSP
      ONE_DSP: if (DATA_WIDTH = 96) generate
         UO: entity work.xor96
            generic map (
               IREG => IREG,
               OREG => OREG
            )
            port map (
               CLK => CLK,
               RESET => RESET,
               DI => DI,
               DO_96 => DO_1,
               DO_2x48 => DO_2,
               DO_4x24 => DO_4,
               CEI => CEI,
               CEO => CEO
            );
      end generate ONE_DSP;

      -- Generation of DSP cascade --
      FIRST_DSP: if (I = 0) and (DATA_WIDTH /= 96) generate
         UF: entity work.xor_first
            generic map (
               IREG => IREG
            )
            port map (
               CLK => CLK,
               RESET => RESET,
               DI => d(I),
               PCOUT => casc(casc'LENGTH-1 downto casc'LENGTH-48),
               CEI => CEI
            );
      end generate FIRST_DSP;

      MIDDLE_DSP: if (I /= 0) and (I /= c_dsp-1) generate
          UM: entity work.xor_middle
            generic map (
               IREG => IREG
            )
            port map (
               CLK => CLK,
               RESET => RESET,
               DI => d(I),
               PCIN => casc(casc'LENGTH-1-48*(I-1) downto casc'LENGTH-48*I),
               PCOUT => casc(casc'LENGTH-1-48*I downto casc'LENGTH-48*(I+1)),
               CEI => CEI
            );
      end generate MIDDLE_DSP;

      LAST_DSP: if (I = c_dsp-1) and (DATA_WIDTH /= 96) generate
         UL: entity work.xor_last
            generic map (
               IREG => IREG,
               OREG => OREG
            )
            port map (
               CLK => CLK,
               RESET => RESET,
               DI => d(I),
               PCIN => casc(casc'LENGTH-1-48*(I-1) downto 0),
               DO => xorout,
               CEI => CEI,
               CEO => CEO
            );

            -- Outputs of wide XOR function --
            DO_1 <= xorout(3);
            DO_2 <= xorout(5) & xorout (1);
            DO_4 <= xorout(6) & xorout(4) & xorout(2) & xorout(0);
      end generate LAST_DSP;

   end generate;

end architecture;
