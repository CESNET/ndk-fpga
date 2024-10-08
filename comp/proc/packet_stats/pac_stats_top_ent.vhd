-- Copyright (C) 2016 CESNET
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

entity PAC_STATS is
   generic(
      EN_DSP            : boolean := true;
      NUM_BYTES_WD      : integer := 48;
      NUM_PACKETS_WD    : integer := 48;
      PACKET_LENGTH_WD  : integer := 16;
      REG_OUT           : integer := 0;
      ADDRESS_WIDTH     : integer := 10
   );
   port(
      CLK               : in  std_logic;
      RESET             : in  std_logic;

      RM_ADDRESS        : in  std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      RM_RD_ENABLE      : in  std_logic;
      RM_REQ            : in  std_logic;

      CNT_ADDRESS       : in  std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      PACKET_LENGTH     : in  std_logic_vector(PACKET_LENGTH_WD-1 downto 0);
      ADD_PACKET        : in  std_logic;
      SRC_RDY           : in  std_logic;
      DST_RDY           : out std_logic;

      RD_NUM_BYTES      : out std_logic_vector(NUM_BYTES_WD-1 downto 0);
      RD_NUM_PACKETS    : out std_logic_vector(NUM_PACKETS_WD-1 downto 0);
      RD_VLD            : out std_logic;
      RD_NEXT           : in  std_logic
   );
end entity;

