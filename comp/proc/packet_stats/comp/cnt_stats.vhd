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
entity CNT_STATS is
   generic (
      EN_DSP            : boolean := true;
      NUM_BYTES_WD      : integer := 48;
      NUM_PACKETS_WD    : integer := 48;
      PACKET_LENGTH_WD  : integer := 16;
      REG_OUT           : integer := 0
   );
   port (
      CLK               : in  std_logic;
      RESET             : in  std_logic;
      PACKET_LENGTH     : in  std_logic_vector(PACKET_LENGTH_WD-1 downto 0);
      ADD_PACKET        : in  std_logic;
      RST_COUNTERS      : in  std_logic;
      IN_NUM_BYTES      : in  std_logic_vector(NUM_BYTES_WD-1 downto 0);
      IN_NUM_PACKETS    : in  std_logic_vector(NUM_PACKETS_WD-1 downto 0);
      OUT_NUM_BYTES     : out std_logic_vector(NUM_BYTES_WD-1 downto 0);
      OUT_NUM_PACKETS   : out std_logic_vector(NUM_PACKETS_WD-1 downto 0)
   );
end entity;

--! Vitrex-7 architecture of ALU48
architecture FULL of CNT_STATS is
begin

   FIRST_CNT_i : entity work.ALU_STATS
   generic map (
      EN_DSP   => EN_DSP,
      A_WIDTH  => NUM_BYTES_WD,
      B_WIDTH  => PACKET_LENGTH_WD,
      P_WIDTH  => NUM_BYTES_WD,
      REG_OUT  => REG_OUT
   )
   port map (
      CLK      => CLK,
      RESET    => RESET,
      EN_ADD   => ADD_PACKET,
      RST_ADD  => RST_COUNTERS,
      A        => IN_NUM_BYTES,
      B        => PACKET_LENGTH,
      P        => OUT_NUM_BYTES
   );

   SECOND_CNT_i : entity work.ALU_STATS
   generic map (
      EN_DSP   => EN_DSP,
      A_WIDTH  => NUM_PACKETS_WD,
      B_WIDTH  => 1,
      P_WIDTH  => NUM_PACKETS_WD,
      REG_OUT  => REG_OUT
   )
   port map (
      CLK      => CLK,
      RESET    => RESET,
      EN_ADD   => ADD_PACKET,
      RST_ADD  => RST_COUNTERS,
      A        => IN_NUM_PACKETS,
      B        => "1",
      P        => OUT_NUM_PACKETS
   );

end architecture;
