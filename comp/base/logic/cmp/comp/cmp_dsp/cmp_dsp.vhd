--! cmp_dsp.vhd
--!
--! \file
--! \brief generic comparator implemented with Virtex-7 DSP slices
--! \author Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;

architecture structural of CMP_DSP is
   type p_pom_t is array (0 to ((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 1)) of std_logic_vector(1 downto 0);
   signal p_pom   : p_pom_t;
   type dec_pom_t is array (0 to ((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 2)) of std_logic_vector(1 downto 0);
   signal dec_pom : dec_pom_t;

begin
   --! generate decoders
   GEN_DECODERS: if(DATA_WIDTH > 48) generate
      dec_pom(0) <= p_pom(0);

      --! generate decoders before last
      GEN_FOR: for I in 0 to ((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 3) generate
         CMP_DECODE_inst: entity work.CMP_DECODE
         port map (
            L_IN => dec_pom(I),
            H_IN => p_pom(I + 1),
            P => dec_pom(I + 1)
         );
      end generate;

      -- generate last decoder
      CMP_DECODE_inst: entity work.CMP_DECODE
      port map (
         L_IN => dec_pom(((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 2)),
         H_IN => p_pom((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 1),
         P => P
      );
   end generate;


   GEN_ALU_DIV: for I in 0 to (DATA_WIDTH/48)-1 generate
   begin
      --! generate DSP only for 48 bit
      GEN_PORT_REG_ONE_48: if(DATA_WIDTH = 48) generate
         CMP48_inst: entity work.CMP48
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
            P => P
         );
      end generate;

      --! generate DSPs when DATA_WIDTH > 48
      GEN_PORT_BETWEEN: if(DATA_WIDTH > 48) generate
      begin
         CMP48_inst: entity work.CMP48
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
            P => p_pom(I)
         );
       end generate;
   end generate;

   GEN_ALU_MOD: if (DATA_WIDTH mod 48 > 0) generate
      signal Amod : std_logic_vector(47 downto 0);
      signal Bmod : std_logic_vector(47 downto 0);
   begin
      Amod((DATA_WIDTH mod 48)-1 downto 0) <= A(A'LENGTH-1 downto A'LENGTH-1-(DATA_WIDTH mod 48)+1);
      Amod(47 downto (DATA_WIDTH mod 48)) <= (others => '0');
      Bmod((DATA_WIDTH mod 48)-1 downto 0) <= B(B'LENGTH-1 downto B'LENGTH-1-(DATA_WIDTH mod 48)+1);
      Bmod(47 downto (DATA_WIDTH mod 48)) <= (others => '0');

      --! generate one DSP when DATA_WIDTH < 48
      GEN_DSP_ONE: if(DATA_WIDTH < 48) generate
         CMP48_inst: entity work.CMP48
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
            P => P
         );
      end generate;

      --! generate last DSP when DATA_WIDTH mod 48 /= 0
      GEN_DSP_LAST: if(DATA_WIDTH > 48) generate

         CMP48_inst: entity work.CMP48
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
            P => p_pom(((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) + 1)) - 1))
         );
      end generate;
   end generate;
end architecture;
