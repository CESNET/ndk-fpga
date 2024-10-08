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

architecture full of PAC_STATS is
   signal tran_CNT_ADDRESS   : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal tran_PACKET_LENGTH : std_logic_vector(PACKET_LENGTH_WD-1 downto 0);
   signal tran_ADD_PACKET    : std_logic;
   signal tran_RST_COUNTERS  : std_logic;
begin

   TRAN_i : entity work.TRANS_STATS
   generic map(
      PACKET_LENGTH_WD  => PACKET_LENGTH_WD,
      ADDRESS_WIDTH     => ADDRESS_WIDTH
   )
   port map(
      CLK               => CLK,
      RESET             => RESET,
      RM_ADDRESS        => RM_ADDRESS,
      RM_RD_ENABLE      => RM_RD_ENABLE,
      RM_REQ            => RM_REQ,
      IN_CNT_ADDRESS    => CNT_ADDRESS,
      IN_PACKET_LENGTH  => PACKET_LENGTH,
      IN_ADD_PACKET     => ADD_PACKET,
      IN_SRC_RDY        => SRC_RDY,
      IN_DST_RDY        => DST_RDY,
      OUT_CNT_ADDRESS   => tran_CNT_ADDRESS,
      OUT_PACKET_LENGTH => tran_PACKET_LENGTH,
      OUT_ADD_PACKET    => tran_ADD_PACKET,
      OUT_RST_COUNTERS  => tran_RST_COUNTERS
   );

   STATS_i : entity work.STATS
   generic map (
      EN_DSP            => EN_DSP,
      NUM_BYTES_WD      => NUM_BYTES_WD,
      NUM_PACKETS_WD    => NUM_PACKETS_WD,
      PACKET_LENGTH_WD  => PACKET_LENGTH_WD,
      REG_OUT           => REG_OUT,
      ADDRESS_WIDTH     => ADDRESS_WIDTH
   )
   port map (
      CLK               => CLK,
      RESET             => RESET,

      CNT_ADDRESS       => tran_CNT_ADDRESS,
      PACKET_LENGTH     => tran_PACKET_LENGTH,
      ADD_PACKET        => tran_ADD_PACKET,
      RST_COUNTERS      => tran_RST_COUNTERS,

      R_NUM_BYTES       => RD_NUM_BYTES,
      R_NUM_PACKETS     => RD_NUM_PACKETS,
      R_VLD             => RD_VLD,
      R_NEXT            => RD_NEXT
   );

end architecture;
