--! alu_dsp.vhd
--!
--! \file
--! \brief ALU implemented with Virtex-7 DSP slices
--! \author Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;

entity ALU_DSP is
   generic (
      DATA_WIDTH  : integer;
      --! Input pipeline registers
      REG_IN      : integer := 0;
      --! Output pipeline register
      REG_OUT     : integer := 0;
      --!
      EN_PIPE     : integer := 0
   );
   port (
      --! Clock input
      CLK         : in  std_logic;
      --! Reset input
      RESET       : in  std_logic;
      --! Data input
      A           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Data input
      B           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Clock enable for input pipeline registers
      CE_IN       : in  std_logic;
      --! Clock enable for output pipeline registers
      CE_OUT      : in  std_logic;

      --! control alu
      --! operators (A [operator] B):
      --!     "0000" -> ADD  (A + B + CARRY_IN)
      --!
      --!     "0001" -> SUB (A - (B + CARRY_IN))
      --!     (WARNING for SUB: when "DATA_WIDTH <= 48" or "DATA_WIDTH mod 48 = 0"
      --!      CARRY_OUT is inverted)
      --!
      --!     "0010" -> NAND
      --!     "0011" -> AND
      --!     "0100" -> OR
      --!     "0101" -> NOR
      --!     "0110" -> ALU
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
      P           : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end ALU_DSP;

architecture structural of ALU_DSP is
   signal in_out_Vector    : std_logic_vector( (DATA_WIDTH/48) downto 0);

begin
   --! first carry_in value
   in_out_Vector(0) <= CARRY_IN;

   GEN_ALU_DIV: for I in 0 to (DATA_WIDTH/48)-1 generate
   begin
      --! generate only for 48 bit
      GEN_PORT_REG_ONE_48: if(DATA_WIDTH = 48) generate
         ALU48_inst: entity work.ALU48
         generic map(
            REG_IN  => REG_IN,
            REG_OUT => REG_OUT
         )
         port map (
            CLK => CLK,
            RESET => RESET,
            A => A(47+I*48 downto 0+I*48),
            B => B(47+I*48 downto 0+I*48),
            CE_IN => CE_IN,
            CE_OUT => CE_OUT,
            ALUMODE => ALUMODE,
            CARRY_IN => in_out_Vector(I),
            CARRY_OUT => in_out_Vector(I+1),
            P => P(47+I*48 downto 0+I*48)
         );
      end generate;

      --! genarate first DSP
      GEN_PORT_FIRST: if(I = 0 and DATA_WIDTH /= 48) generate
         signal p_pom    : std_logic_vector(47 downto 0);
      begin
         --! generate output registers
         GEN_OUT_REG: if(REG_OUT = 1) generate
            process(CLK)
            begin
               if (CLK'event) and (CLK='1') then
                  if (RESET='1') then
                     P(47+I*48 downto 0+I*48) <= (others => '0');
                  elsif (CE_OUT='1') then
                     P(47+I*48 downto 0+I*48) <= p_pom;
                  end if;
               end if;
            end process;
         end generate;

         --! generate connection without registers
         GEN_OUT_OFF_REG: if(REG_OUT = 0) generate
            P(47+I*48 downto 0+I*48) <= p_pom;
         end generate;

         ALU48_inst: entity work.ALU48
         generic map(
            REG_IN  => REG_IN,
            REG_OUT => EN_PIPE,
            SWITCH_CARRY_OUT => 1
         )
         port map (
            CLK => CLK,
            RESET => RESET,
            A => A(47+I*48 downto 0+I*48),
            B => B(47+I*48 downto 0+I*48),
            CE_IN => CE_IN,
            CE_OUT => CE_OUT,
            ALUMODE => ALUMODE,
            CARRY_IN => in_out_Vector(I),
            CARRY_OUT => in_out_Vector(I+1),
            P => p_pom
         );
      end generate;

      --! generate DSPs between first and last
      GEN_PORT_BETWEEN: if((I > 0) and ((I < ((DATA_WIDTH/48) -1)) OR ((DATA_WIDTH mod 48) > 0))) generate
         signal p_pom    : std_logic_vector(47 downto 0);
         signal pipe_in   : std_logic_vector(95 downto 0);
         signal pipe_out  : std_logic_vector(95 downto 0);
      begin
         --! generate output registers
         GEN_OUT_REG: if(REG_OUT = 1) generate
            process(CLK, CE_OUT)
            begin
               if (CLK'event) and (CLK='1') then
                  if (RESET='1') then
                     P(47+I*48 downto 0+I*48) <= (others => '0');
                  elsif (CE_OUT='1') then
                     P(47+I*48 downto 0+I*48) <= p_pom;
                  end if;
               end if;
            end process;
         end generate;

         --! generate connection without registers
         GEN_OUT_OFF_REG: if(REG_OUT = 0) generate
            P(47+I*48 downto 0+I*48) <= p_pom;
         end generate;

         pipe_in <= A(47+I*48 downto 0+I*48) & B(47+I*48 downto 0+I*48);
         IF_PIPE_GEN: if(EN_PIPE = 1) generate
            PIPE_inst: entity work.PIPE_DSP
            generic map(
               PIPE_EN     => true,
               DATA_WIDTH  => 96,
               ENABLE_DSP  => false,
               NUM_REGS    => I
            )
            port map(
               CLK         => CLK,
               RESET       => RESET,
               DATA_IN     => pipe_in,
               DATA_OUT    => pipe_out,
               CE          => '1'
            );
         end generate;

         PIPE_GEN: if(EN_PIPE = 0) generate
            pipe_out <= A(47+I*48 downto 0+I*48) & B(47+I*48 downto 0+I*48);
         end generate;

         ALU48_inst: entity work.ALU48
         generic map(
            REG_IN  => (2 * (REG_IN mod 2)),
            REG_OUT => EN_PIPE,
            SWITCH_CARRY => 1,
            SWITCH_CARRY_OUT => 1
         )
         port map (
            CLK => CLK,
            RESET => RESET,
            A => pipe_out(95 downto 48),
            B => pipe_out(47 downto 0),
            CE_IN => CE_IN,
            CE_OUT => CE_OUT,
            ALUMODE => ALUMODE,
            CARRY_IN => in_out_Vector(I),
            CARRY_OUT => in_out_Vector(I+1),
            P => p_pom
         );
      end generate;

      --! generate last DSP when DATA_WIDTH mod 48 = 0
      GEN_PORT_LAST: if((I > 0) and I = ((DATA_WIDTH/48) - 1) and (DATA_WIDTH mod 48) = 0) generate
         signal pipe_in   : std_logic_vector(95 downto 0);
         signal pipe_out  : std_logic_vector(95 downto 0);
      begin
         pipe_in <= A(47+I*48 downto 0+I*48) & B(47+I*48 downto 0+I*48);
         IF_PIPE_GEN: if(EN_PIPE = 1) generate
            PIPE_inst: entity work.PIPE_DSP
            generic map(
               PIPE_EN     => true,
               DATA_WIDTH  => 96,
               ENABLE_DSP  => false,
               NUM_REGS    => I
            )
            port map(
               CLK         => CLK,
               RESET       => RESET,
               DATA_IN     => pipe_in,
               DATA_OUT    => pipe_out,
               CE          => '1'
            );
         end generate;

         PIPE_GEN: if(EN_PIPE = 0) generate
            pipe_out <= A(47+I*48 downto 0+I*48) & B(47+I*48 downto 0+I*48);
         end generate;

         ALU48_inst: entity work.ALU48
         generic map(
            REG_IN  => (2 * (REG_IN mod 2)),
            REG_OUT => REG_OUT,
            SWITCH_CARRY => 1
         )
         port map (
            CLK => CLK,
            RESET => RESET,
            A => pipe_out(95 downto 48),
            B => pipe_out(47 downto 0),
            CE_IN => CE_IN,
            CE_OUT => CE_OUT,
            ALUMODE => ALUMODE,
            CARRY_IN => in_out_Vector(I),
            CARRY_OUT => in_out_Vector(I+1),
            P => P(47+I*48 downto 0+I*48)
         );
      end generate;
   end generate;

   --! generate connection CARYY_OUT
   GEN_ALU_OUT: if (DATA_WIDTH mod 48 = 0) generate
        CARRY_OUT <= in_out_Vector(DATA_WIDTH/48);
   end generate;

   -- generate last DSPs when DATA_WIDTH mod 48 /= 0
   GEN_ALU_MOD: if (DATA_WIDTH mod 48 > 0) generate
      signal Amod : std_logic_vector(47 downto 0);
      signal Bmod : std_logic_vector(47 downto 0);
      signal Pmod : std_logic_vector(47 downto 0);
   begin
      Amod((DATA_WIDTH mod 48)-1 downto 0) <= A(A'LENGTH-1 downto A'LENGTH-1-(DATA_WIDTH mod 48)+1);
      Amod(47 downto (DATA_WIDTH mod 48)) <= (others => '0');
      Bmod((DATA_WIDTH mod 48)-1 downto 0) <= B(B'LENGTH-1 downto B'LENGTH-1-(DATA_WIDTH mod 48)+1);
      Bmod(47 downto (DATA_WIDTH mod 48)) <= (others => '0');

      --! generate one DSP when DATA_WIDTH < 48
      GEN_DSP_ONE: if(DATA_WIDTH < 48) generate
         ALU48_inst: entity work.ALU48
         generic map (
            REG_IN => REG_IN,
            REG_OUT => REG_OUT
         )
         port map (
            CLK => CLK,
            RESET => RESET,
            A => Amod,
            B => Bmod,
            CE_IN => CE_IN,
            CE_OUT => CE_OUT,
            ALUMODE => ALUMODE,
            CARRY_IN => in_out_Vector(DATA_WIDTH/48),
            CARRY_OUT => open,
            P => Pmod
         );
      end generate;

      --! generate last DSP when DATA_WIDTH mod 48 /= 0
      GEN_DSP_LAST: if(DATA_WIDTH > 48) generate
         signal pipe_in   : std_logic_vector(95 downto 0);
         signal pipe_out  : std_logic_vector(95 downto 0);
      begin
         pipe_in <= Amod & Bmod;
         IF_PIPE_GEN: if(EN_PIPE = 1) generate
            PIPE_inst: entity work.PIPE_DSP
            generic map(
               PIPE_EN     => true,
               DATA_WIDTH  => 96,
               ENABLE_DSP  => false,
               NUM_REGS    => (DATA_WIDTH/48)
            )
            port map(
               CLK         => CLK,
               RESET       => RESET,
               DATA_IN     => pipe_in,
               DATA_OUT    => pipe_out,
               CE          => '1'
            );
         end generate;

         PIPE_GEN: if(EN_PIPE = 0) generate
            pipe_out <= Amod & Bmod;
         end generate;

         ALU48_inst: entity work.ALU48
         generic map (
            REG_IN => 2 *(REG_IN mod 2),
            REG_OUT => REG_OUT,
            SWITCH_CARRY => 1
         )
         port map (
            CLK => CLK,
            RESET => RESET,
            A => pipe_out(95 downto 48),
            B => pipe_out(47 downto 0),
            CE_IN => CE_IN,
            CE_OUT => CE_OUT,
            ALUMODE => ALUMODE,
            CARRY_IN => in_out_Vector(DATA_WIDTH/48),
            CARRY_OUT => open,
            P => Pmod
         );
      end generate;

      CARRY_OUT <= Pmod(DATA_WIDTH mod 48);
      P(P'LENGTH-1 downto P'LENGTH-1-(DATA_WIDTH mod 48)+1) <= Pmod((DATA_WIDTH mod 48)-1 downto 0);
   end generate;
end architecture;
