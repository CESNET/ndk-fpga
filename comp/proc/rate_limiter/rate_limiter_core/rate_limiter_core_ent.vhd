-- rate_limiter_core_ent.vhd
--!
--! \file  rate_limiter_core_ent.vhd
--! \brief Interfaces for packet rate limiter
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

entity rate_lim is

   generic (
      ADDR_WIDTH   : integer := 8;
      LIMIT_WIDTH  : integer := 16;  --! maximal value: 17
      SPEED_WIDTH  : integer := 20;  --! maximal value: 24
      CONST_WIDTH  : integer := 10   --! maximal value: 17
   );
   port (
      CLK          : in std_logic;
      RESET        : in std_logic;
      --! packet info
      PACKET_LEN   : in std_logic_vector(15 downto 0);
      PACKET_TS    : in std_logic_vector(63 downto 0); --! time stemp, unit: ns
      --! bucket record
      RECORD_ADDR  : in std_logic_vector(ADDR_WIDTH-1 downto 0);
      ADDR_VLD     : in std_logic;
      BUCKET_VALUE : in std_logic_vector(SPEED_WIDTH+LIMIT_WIDTH-1 downto 0); --! amount of avaliable tokens
      BUCKET_TS    : in std_logic_vector(63 downto 0); --! time stemp, unit: ns
      BUCKET_LIMIT : in std_logic_vector(LIMIT_WIDTH-1 downto 0);
      SPEED        : in std_logic_vector(SPEED_WIDTH-1 downto 0); --! unit: TOKENS per BYTE
      TIME_CONST   : in std_logic_vector(CONST_WIDTH-1 downto 0); --! unit: TOKENs per ns

      --! packet passed signal
      PASS            : out std_logic;
      --! renew bucket record
      BUCKET_WE       : out std_logic;
      RECORD_ADDR_OUT : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      BUCKET_VAL_OUT  : out std_logic_vector(SPEED_WIDTH+LIMIT_WIDTH-1 downto 0);
      BUCKET_TS_OUT   : out std_logic_vector(63 downto 0);

      IN_SRC_RDY   : in  std_logic;
      IN_DST_RDY   : out std_logic;
      OUT_SRC_RDY  : out std_logic;
      OUT_DST_RDY  : in  std_logic
   );

end entity rate_lim;
