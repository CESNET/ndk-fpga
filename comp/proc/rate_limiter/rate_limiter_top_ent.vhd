-- rate_limiter_top_ent.vhd
--!
--! \file  rate_limiter_top_ent.vhd
--! \brief Interfaces for top architecture of packet rate limiter
--!
--! \Author: Jakub Lukac <xlukac09@stud.fit.vutbr.cz>
--! \date 2015
--!
--! \section License
--!
--! Copyright (C) 2015 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity rate_lim_top is

   generic (
      ITEMS_IN_MEM   : integer := 1024;
      LIMIT_WIDTH    : integer := 16;  --! maximal value: 17
      SPEED_WIDTH    : integer := 20;  --! maximal value: 24
      CONST_WIDTH    : integer := 10   --! maximal value: 17
   );
   port (
      CLK         : in std_logic;
      RESET       : in std_logic;
      --! packet info
      PACKET_LEN  : in std_logic_vector(15 downto 0);
      PACKET_TS   : in std_logic_vector(63 downto 0); --! time stemp, unit: ns
      --! bucket record address
      RECORD_ADDR : in std_logic_vector(log2(ITEMS_IN_MEM)-1 downto 0);
      ADDR_VLD    : in std_logic;

      --! packet passed signal
      PASS        : out std_logic;

      --! source destination ready interfaces
      IN_SRC_RDY  : in  std_logic; -- source is ready to send data
      IN_DST_RDY  : out std_logic; -- rate_limiter is ready to receive data
      OUT_SRC_RDY : out std_logic; -- rate_limiter is ready to send data
      OUT_DST_RDY : in  std_logic; -- destination is ready to receive data

      --! MI32 interface
      ------------------------------------------------
      --! Address
      MI32_ADDR   : in std_logic_vector(31 downto 0);
      --! Write request
      MI32_WR     : in std_logic;
      --! Input data
      MI32_DWR    : in std_logic_vector(31 downto 0);
      --! Read request
      MI32_RD     : in std_logic;
      --! Output data
      MI32_DRD    : out std_logic_vector(31 downto 0);
      --! Data ready
      MI32_DRDY   : out std_logic;
      --! Address ready
      MI32_ARDY   : out std_logic;
      --! Byte enable
      MI32_BE     : in std_logic_vector(3 downto 0)
      ------------------------------------------------
   );

end rate_lim_top;
