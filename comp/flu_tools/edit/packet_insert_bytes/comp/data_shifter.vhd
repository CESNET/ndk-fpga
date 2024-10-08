--
-- Copyright (C) 2015 CESNET
-- Author(s): Mário Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

entity DATA_SHIFTER is
   generic(
      DATA_WIDTH  : integer := 512;
      --! enable mem
      MEM_EN      : boolean := false;
      --! enable input pipe
      IN_PIPE     : boolean := false
   );
   port(
      CLK         : in std_logic;
      RESET       : in std_logic;
      --! constrol select signal of multiplexers
      MUX_SELS    : in std_logic_vector((DATA_WIDTH/8)/4 - 1 downto 0);
      --! input data
      DATA_IN     : in std_logic_vector(DATA_WIDTH - 1 downto 0);
      --! output data
      DATA_OUT    : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      SRC_RDY     : in std_logic;
      DST_RDY     : in std_logic
);
end entity;

architecture full of DATA_SHIFTER is
   signal mem_out       : std_logic_vector(31 downto 0);
   signal pipe_DATA_IN  : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal pipe_MUX_SELS : std_logic_vector(MUX_SELS'length-1 downto 0);
   signal pipe_SRC_RDY  : std_logic;
   signal pause         : std_logic;
begin

   INPUT_PIPE: if(IN_PIPE = true) generate
      process(CLK)
      begin
         if (CLK'event) and (CLK='1') then
            pipe_MUX_SELS  <= MUX_SELS;
            pipe_DATA_IN   <= DATA_IN;
            pipe_SRC_RDY   <= SRC_RDY;
         end if;
      end process;
   end generate;

   INPUT_PIPE_off: if(IN_PIPE = false) generate
      pipe_MUX_SELS  <= MUX_SELS;
      pipe_DATA_IN   <= DATA_IN;
      pipe_SRC_RDY   <= SRC_RDY;
   end generate;

   pause <= DST_RDY and pipe_SRC_RDY;

   -- geneate memory for last block
   GEN_MEM: if(MEM_EN = true) generate
     process(CLK)
      begin
         if (CLK'event) and (CLK='1') then
            if(RESET = '1') then
               mem_out <= (others => '0');
            elsif(pause = '1') then
               mem_out <= pipe_DATA_IN(DATA_WIDTH-1 downto DATA_WIDTH-32);
            end if;
         end if;
      end process;
   end generate;

   GEN_MEM_NO: if(MEM_EN = false) generate
      mem_out <= (others => '0');
   end generate;

   -- generate multiplexers
   GEN_MUXs: for I in 0 to ((DATA_WIDTH/8)/4) - 1 generate
      signal tmp_mux_out   : std_logic_vector(31 downto 0);
      signal tmp_mux_in    : std_logic_vector(64-1 downto 0);
   begin
      GNE_FIRST: if(I = 0) generate
         tmp_mux_in(63 downto 32)   <= mem_out;
         tmp_mux_in(31 downto 0)    <= pipe_DATA_IN(31+(I*32) downto I*32);
      end generate;

      GNE_OTHERS: if(I /= 0) generate
         tmp_mux_in(63 downto 32)   <= pipe_DATA_IN(31+((I-1)*32) downto (I-1)*32);
         tmp_mux_in(31 downto 0)    <= pipe_DATA_IN(31+(I*32) downto I*32);
      end generate;

      -- connect multiplexer
      MUX_inst: entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => 32,
         MUX_WIDTH   => 2
      )
      port map(
         DATA_IN     => tmp_mux_in,
         SEL         => pipe_MUX_SELS(I downto I),
         DATA_OUT    => tmp_mux_out
      );

      DATA_OUT(31+(I*32) downto I*32) <= tmp_mux_out;
   end generate;
end architecture;

