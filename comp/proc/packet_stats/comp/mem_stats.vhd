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
entity MEM_STATS is
   generic (
      NUM_BYTES_WD      : integer := 48;
      NUM_PACKETS_WD    : integer := 48;
      ADDRESS_WIDTH     : integer := 10
   );
   port (
      CLK               : in std_logic;
      RESET             : in std_logic;
      RD_NUM_BYTES      : out std_logic_vector(NUM_BYTES_WD-1 downto 0);
      RD_NUM_PACKETS    : out std_logic_vector(NUM_PACKETS_WD-1 downto 0);
      RD_ADDRESS        : in std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      WR_NUM_BYTES      : in std_logic_vector(NUM_BYTES_WD-1 downto 0);
      WR_NUM_PACKETS    : in std_logic_vector(NUM_PACKETS_WD-1 downto 0);
      WR_ADDRESS        : in std_logic_vector(ADDRESS_WIDTH-1 downto 0)
   );
end entity;

--! Vitrex-7 architecture of ALU48
architecture FULL of MEM_STATS is
   constant bram_width     : integer := NUM_BYTES_WD + NUM_PACKETS_WD;
   signal bram_rd          : std_logic_vector(bram_width-1 downto 0);
   signal bram_wr          : std_logic_vector(bram_width-1 downto 0);
   signal pipe_bram_wr     : std_logic_vector(bram_width-1 downto 0);
   signal address_cmp      : std_logic;
   signal pipe_address_cmp : std_logic;
begin

   address_cmp <= '1' when WR_ADDRESS = RD_ADDRESS else
                  '0';

   -- register mux pipe ------------------------------------------------------
   muxp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         pipe_address_cmp <= address_cmp;
         pipe_bram_wr <= bram_wr;
      end if;
   end process;

   RD_NUM_BYTES   <= bram_rd(NUM_BYTES_WD-1 downto 0) when pipe_address_cmp = '0' else
                     pipe_bram_wr(NUM_BYTES_WD-1 downto 0);
   RD_NUM_PACKETS <= bram_rd(NUM_PACKETS_WD + NUM_BYTES_WD-1 downto NUM_BYTES_WD) when pipe_address_cmp = '0' else
                     pipe_bram_wr(NUM_PACKETS_WD + NUM_BYTES_WD-1 downto NUM_BYTES_WD);

   bram_wr <= WR_NUM_PACKETS & WR_NUM_BYTES;

   BRAM_i : entity work.DP_BRAM_V7
   generic map (
      DATA_WIDTH     => bram_width,
      ADDRESS_WIDTH  => ADDRESS_WIDTH
   )
   port map (
      CLKA     => CLK,
      RSTA     => RESET,
      PIPE_ENA => '1',
      REA      => '1',
      WEA      => '0',
      ADDRA    => RD_ADDRESS,
      DIA      => (others => '0'),
      DOA_DV   => open,
      DOA      => bram_rd,

      CLKB     => CLK,
      RSTB     => RESET,
      PIPE_ENB => '1',
      REB      => '0',
      WEB      => '1',
      ADDRB    => WR_ADDRESS,
      DIB      => bram_wr,
      DOB_DV   => open,
      DOB      => open
   );
end architecture;
