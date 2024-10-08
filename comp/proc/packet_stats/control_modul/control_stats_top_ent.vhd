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

entity CONTROL_STATS is
   generic(
      EN_DSP            : boolean := true;
      PACKET_LENGTH_WD  : integer := 16;
      NUM_BYTES_WD      : integer := 48;
      NUM_PACKETS_WD    : integer := 48;
      ADDRESS_WIDTH     : integer := 10
   );
   port(
      CLK               : in  std_logic;
      RESET             : in  std_logic;
      --! MI32 interface
      MI32_ADDR         : in std_logic_vector(31 downto 0);
      MI32_WR           : in std_logic;
      MI32_DWR          : in std_logic_vector(31 downto 0);
      MI32_RD           : in std_logic;
      MI32_DRD          : out std_logic_vector(31 downto 0);
      MI32_DRDY         : out std_logic;
      MI32_ARDY         : out std_logic;
      MI32_BE           : in std_logic_vector(3 downto 0);
      --! add packets
      CNT_ADDRESS       : in  std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      PACKET_LENGTH     : in  std_logic_vector(PACKET_LENGTH_WD-1 downto 0);
      ADD_PACKET        : in  std_logic;
      SRC_RDY           : in  std_logic;
      DST_RDY           : out std_logic
    );
end entity;

