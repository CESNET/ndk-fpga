--! mux_dsp.vhd
--!
--! \file
--! \author Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2015
--!
--! \section License
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;

entity MUX_DSP is
   generic (
      DATA_WIDTH  : integer := 48;
      --! Input pipeline registers (0, 1)
      REG_IN_A    : integer := 1;
      REG_IN_B    : integer := 1;
      REG_SEL     : integer := 1;
      --! Output pipeline register (0, 1)
      REG_OUT     : integer := 1;
      --!
      EN_CASCADE_IN  : boolean := false;
      NEG_SEL        : boolean := false
   );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;
      --! Data input
      A        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Data input
      B        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Clock enable for input pipeline registers
      CE_IN_A  : in  std_logic;
      CE_IN_B  : in  std_logic;
      CE_SEL   : in  std_logic;
      --! '0' -> A, '1' -> B
      SEL      : in std_logic;
      --! Clock enable for output pipeline registers
      CE_OUT   : in  std_logic;
      --! output
      P        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      P_CAS    : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end MUX_DSP;

architecture full of MUX_DSP is
   constant NUM : integer := DATA_WIDTH/48;
begin

   GEN_MUX: for I in 0 to NUM generate

      GEN_OTHERS: if (I < NUM) generate
         signal tmp_P_OUT      : std_logic_vector(47 downto 0);
         signal tmp_P_CAS_OUT  : std_logic_vector(47 downto 0);
      begin
         P_CAS(47+I*48 downto 0+I*48) <= tmp_P_CAS_OUT;
         P(47+I*48 downto 0+I*48) <= tmp_P_OUT;

         MUX48_inst: entity work.MUX48
         generic map(
            REG_IN_A  => REG_IN_A,
            REG_IN_B  => REG_IN_B,
            REG_SEL   => REG_SEL,
            REG_OUT   => REG_OUT,
            CASCADE_EN => EN_CASCADE_IN,
            NEG_SEL    => NEG_SEL
         )
         port map (
            CLK => CLK,
            RESET => RESET,
            A => A(47+I*48 downto 0+I*48),
            B => B(47+I*48 downto 0+I*48),
            CE_IN_A => CE_IN_A,
            CE_IN_B => CE_IN_B,
            CE_SEL  => CE_SEL,
            CE_OUT => CE_OUT,
            SEL => SEL,
            P => tmp_P_OUT,
            P_CAS => tmp_P_CAS_OUT
         );
      end generate;

      GEN_LAST: if (I = NUM) and (DATA_WIDTH mod 48 /= 0) generate
         constant num_bits : integer := DATA_WIDTH mod 48;
         signal tmp_a : std_logic_vector(47 downto 0);
         signal tmp_b : std_logic_vector(47 downto 0);
         signal tmp_p : std_logic_vector(47 downto 0);
         signal tmp_p_cas : std_logic_vector(47 downto 0);
      begin
         tmp_a(num_bits-1 downto 0) <=  A(DATA_WIDTH-1 downto DATA_WIDTH-num_bits);
         tmp_a(47 downto num_bits)  <=  (others => '0');
         tmp_b(num_bits-1 downto 0) <=  B(DATA_WIDTH-1 downto DATA_WIDTH-num_bits);
         tmp_b(47 downto num_bits)  <=  (others => '0');

         P_CAS(DATA_WIDTH-1 downto DATA_WIDTH-num_bits) <= tmp_p_cas(num_bits-1 downto 0);
         P(DATA_WIDTH-1 downto DATA_WIDTH-num_bits) <= tmp_p(num_bits-1 downto 0);

         MUX48_inst: entity work.MUX48
         generic map(
            REG_IN_A  => REG_IN_A,
            REG_IN_B  => REG_IN_B,
            REG_SEL   => REG_SEL,
            REG_OUT   => REG_OUT,
            CASCADE_EN => EN_CASCADE_IN,
            NEG_SEL    => NEG_SEL
         )
         port map (
            CLK => CLK,
            RESET => RESET,
            A => tmp_a,
            B => tmp_b,
            CE_IN_A => CE_IN_A,
            CE_IN_B => CE_IN_B,
            CE_SEL  => CE_SEL,
            CE_OUT => CE_OUT,
            SEL => SEL,
            P => tmp_p,
            P_CAS => tmp_p_cas
         );
      end generate;
   end generate;
end architecture;
