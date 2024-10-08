-- xor_dsp.vhd
--!
--! \file
--! \brief Parallel bitwise XOR implemented with Virtex-7 DSP slices
--! \author Tomas Zavodnik <xzavod12@stud.fit.vutbr.cz>
--! \date 2013
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;

entity XOR_DSP is
	generic (
		data_width	: integer;
		--! Input pipeline registers
      ABREG			: integer := 0;
      --! Output pipeline register
      PREG			: integer := 0
	);
	port (
		--! Clock input
      CLK      : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;
      --! Data input
      A        : in  std_logic_vector(data_width-1 downto 0);
      --! Data input
      B        : in  std_logic_vector(data_width-1 downto 0);
      --! Clock enable for input pipeline registers
      CEAB     : in  std_logic;
      --! Clock enable for output pipeline registers
      CEP      : in  std_logic;
      --! Data output
      P        : out std_logic_vector(data_width-1 downto 0)
   );
end XOR_DSP;

architecture structural of XOR_DSP is

begin

	GEN_XOR_DIV: for I in 0 to (data_width/48)-1 generate
		XOR48_inst: entity work.XOR48
		generic map (
			ABREG => ABREG,
			PREG => PREG
		)
		port map (
			CLK => CLK,
			RESET => RESET,
			A => A(47+I*48 downto 0+I*48),
			B => B(47+I*48 downto 0+I*48),
			CEAB => CEAB,
			CEP => CEP,
			P => P(47+I*48 downto 0+I*48)
		);
	end generate;

	GEN_XOR_MOD: if (data_width mod 48 > 0) generate
		signal Amod : std_logic_vector(47 downto 0);
		signal Bmod : std_logic_vector(47 downto 0);
		signal Pmod : std_logic_vector(47 downto 0);
	begin
		Amod((data_width mod 48)-1 downto 0) <= A(A'LENGTH-1 downto A'LENGTH-1-(data_width mod 48)+1);
		Amod(47 downto (data_width mod 48)) <= (others => '0');
		Bmod((data_width mod 48)-1 downto 0) <= B(B'LENGTH-1 downto B'LENGTH-1-(data_width mod 48)+1);
		Bmod(47 downto (data_width mod 48)) <= (others => '0');

		XOR48_inst: entity work.XOR48
		generic map (
			ABREG => ABREG,
			PREG => PREG
		)
		port map (
			CLK => CLK,
			RESET => RESET,
			A => Amod,
			B => Bmod,
			CEAB => CEAB,
			CEP => CEP,
			P => Pmod
		);

		P(P'LENGTH-1 downto P'LENGTH-1-(data_width mod 48)+1) <= Pmod((data_width mod 48)-1 downto 0);
	end generate;

end architecture;
