-- Copyright (C) 2016 CESNET
-- Author(s): Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                       ARCHITECTURE DECLARATION                            --
-- ----------------------------------------------------------------------------

architecture full of CONTROL_STATS is
   signal mi_addr           : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal mi_rm             : std_logic;
   signal mi_rd_enable      : std_logic;
   signal mi_ardy           : std_logic;

   signal stats_num_bytes   : std_logic_vector(NUM_BYTES_WD-1 downto 0);
   signal stats_num_packets : std_logic_vector(NUM_PACKETS_WD-1 downto 0);
   signal stats_vld         : std_logic;
   signal stats_next        : std_logic;
begin

   MI32_CONTROL_i : entity work.MI32_CONTROL
   generic map(
      NUM_BYTES_WD     => NUM_BYTES_WD,
      NUM_PACKETS_WD   => NUM_PACKETS_WD,
      ADDRESS_WIDTH    => ADDRESS_WIDTH
   )
   port map(
      CLK              => CLK,
      RESET            => RESET,
      MI32_ADDR        => MI32_ADDR,
      MI32_WR          => MI32_WR,
      MI32_DWR         => MI32_DWR ,
      MI32_RD          => MI32_RD,
      MI32_DRD         => MI32_DRD,
      MI32_DRDY        => MI32_DRDY,
      MI32_ARDY        => MI32_ARDY,
      MI32_BE          => MI32_BE,
      RM_ADDR          => mi_addr,
      RM_RD_ENABLE     => mi_rd_enable,
      RM               => mi_rm,
      RM_ARDY          => mi_ardy,
      CNT_NUM_BYTES    => stats_num_bytes,
      CNT_NUM_PACKETS  => stats_num_packets,
      CNT_VLD          => stats_vld,
      CNT_NEXT         => stats_next
   );
   mi_ardy <= '1';


   PACKET_STAT_i : entity work.PAC_STATS
   generic map(
      EN_DSP            => EN_DSP,
      NUM_BYTES_WD      => NUM_BYTES_WD,
      NUM_PACKETS_WD    => NUM_PACKETS_WD,
      PACKET_LENGTH_WD  => PACKET_LENGTH_WD,
      REG_OUT           => 0,
      ADDRESS_WIDTH     => ADDRESS_WIDTH
   )
   port map(
      CLK               => CLK,
      RESET             => RESET,
      RM_ADDRESS        => mi_addr,
      RM_RD_ENABLE      => mi_rd_enable,
      RM_REQ            => mi_rm,
      CNT_ADDRESS       => CNT_ADDRESS,
      PACKET_LENGTH     => PACKET_LENGTH,
      ADD_PACKET        => ADD_PACKET,
      SRC_RDY           => SRC_RDY,
      DST_RDY           => DST_RDY,
      RD_NUM_BYTES      => stats_num_bytes,
      RD_NUM_PACKETS    => stats_num_packets,
      RD_VLD            => stats_vld,
      RD_NEXT           => stats_next
   );

end architecture;
