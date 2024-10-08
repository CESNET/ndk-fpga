--! \file:   bram_generic.vhd
--! \brief:  Generated memory
--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use IEEE.numeric_std.all;
Library UNISIM;
use UNISIM.vcomponents.all;
use work.math_pack.all;

entity BRAM_GENERATOR is
   generic (
      --! Data width of input/output value
      DATA_WIDTH   : integer := 32;
      --! Number of items in memory
      ITEMS        : integer := 10
   );
   port (
      --! Reset input
      RESET  : in    std_logic;
      --! CLK input
      CLK    : in    std_logic;

      --! \Interface for MI32
      --! Read Enable
      REA    : in    std_logic;
      --! Write enable
      WEA    : in    std_logic;
      --! Address A
      ADDRA  : in    std_logic_vector(29 downto 0);
      --! Data A In
      DIA    : in    std_logic_vector(31 downto 0);
      --! Data A Out
      DOA    : out   std_logic_vector(31 downto 0);

      --- \Interface for generate
      --! Read Enable
      REB    : in    std_logic;
      --! Address B
      ADDRB  : in    std_logic_vector(log2(ITEMS)-1 downto 0);
      --! Data B out
      DOB    : out   std_logic_vector(32*div_roundup(DATA_WIDTH, 32)-1 downto 0)
   );
end BRAM_GENERATOR;

architecture full of BRAM_GENERATOR is
   --! bram + registers
   constant ITEMS_ALL : integer := ITEMS + 16;
   signal addr_pom   : std_logic_vector(log2(ITEMS_All)-1 downto 0);
   --! input demultiplexer
   signal wr_rd_pom   : std_logic_vector(1 downto 0);
   signal demux_out   : std_logic_vector(2*div_roundup(DATA_WIDTH, 32)-1 downto 0);
   --! output multiplexer
   signal mux_in      : std_logic_vector(32*div_roundup(DATA_WIDTH, 32)-1 downto 0);
   signal mux_out     : std_logic_vector(31 downto 0);
   --! address BRAM
   signal addr_bram   : std_logic_vector(log2(ITEMS)-1 downto 0);
   --! adsress demux, mux
   signal addr_mux    : std_logic_vector(max(1,log2(div_roundup(DATA_WIDTH, 32))) - 1 downto  0);
begin
   addr_pom  <= ADDRA(log2(ITEMS_All)-1 downto 0) - 16;
   addr_bram <= addr_pom(log2(ITEMS)-1 downto 0);

   pipe_addr: process(CLK)
   begin
      if(CLK'event) and (CLK='1') then
         addr_mux  <= ADDRA( (max(1,log2(div_roundup(DATA_WIDTH, 32)))-1)+log2(ITEMS_ALL) downto log2(ITEMS_ALL));
      end if;
   end process;

   wr_rd_pom(0) <= WEA;
   wr_rd_pom(1) <= REA;

   --! demultiplexer logic
   GEN_DEMUX: if(div_roundup(DATA_WIDTH, 32) > 1)  generate
      GEN_DEMUX_inst : entity work.GEN_DEMUX
         generic map(
            DATA_WIDTH  => 2,
            DEMUX_WIDTH => div_roundup(DATA_WIDTH, 32)
         )
         port map(
            DATA_IN  => wr_rd_pom,
            SEL      => addr_mux,
            DATA_OUT => demux_out
         );
   end generate;

   --! demultiplexer logic - one BRAM
   GEN_NO_DEMUX: if(div_roundup(DATA_WIDTH, 32) <= 1)  generate
      demux_out <= wr_rd_pom;
   end generate;

   --! multiplexer logic - BRAM 32 bit words
   GEN_MUX_inst : entity work.GEN_MUX
   generic map (
      DATA_WIDTH => 32,
      MUX_WIDTH  => div_roundup(DATA_WIDTH, 32)
   )
   port map(
      DATA_IN    => mux_in,
      SEL        => addr_mux,
      DATA_OUT   => mux_out
   );
   DOA <= mux_out;

   --! generate BRAMs
   GEN_BRAMS : for I in 0 to div_roundup(DATA_WIDTH, 32) - 1 generate
      DP_BRAM_V7_inst : entity work.DP_BRAM_V7
      generic map(
         --! Input data width
         DATA_WIDTH => 32,
         --! Address bus width
         ADDRESS_WIDTH  => log2(ITEMS)
      )
      port map(
         --! Reset only if output_reg
         RSTA => RESET,
         --! \name Interface A
         --! Clock A
         CLKA  => CLK,
         --! Pipe enable
         PIPE_ENA => '1',
         --! Read Enable
         REA => demux_out((I*2) + 1),
         --! Write enable
         WEA => demux_out(I*2),
         --! Address A
         ADDRA => addr_bram,
         --! Data A In
         DIA  => DIA,
         --! Data A Valid
         DOA_DV => open,
         --! Data A Out
         DOA    => mux_in(31+(I*32) downto 0+(I*32)),

         --! \name Interface B
         --! Clock B
         RSTB => RESET,
         --!
         CLKB   => CLK,
         --! Pipe enable
         PIPE_ENB => '1',
         --! Read Enable
         REB    => REB,
         --! Write enable
         WEB    => '0',
         --! Address B
         ADDRB  => ADDRB,
         --! Data B In
         DIB    => (others => '0'),
         --! Data B Valid
         DOB_DV => open,
         --! Data B out
         DOB    => DOB(31+(I*32) downto 0+(I*32))
      );
   end generate;
end full;
