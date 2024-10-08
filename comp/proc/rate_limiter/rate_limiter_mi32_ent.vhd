-- rate_limiter_mi32_ent.vhd
--!
--! \file  rate_limiter_mi32_ent.vhd
--! \brief Interfaces for memory unit with limiting constants
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

entity rate_lim_mi32 is

   generic (
      ADDR_WIDTH     : integer := 8;
      LIMIT_WIDTH    : integer := 16;  --! maximal value: 17
      SPEED_WIDTH    : integer := 20;  --! maximal value: 24
      CONST_WIDTH    : integer := 10   --! maximal value: 17
   );
   port (
      CLK         : in std_logic;
      RESET       : in std_logic;

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
      MI32_BE     : in std_logic_vector(3 downto 0);
      ------------------------------------------------

      --! User interface - read only
      --! Address
      USER_ADDR   : in std_logic_vector(ADDR_WIDTH-1 downto 0);
      --! Read request
      USER_RD     : in std_logic;
      --! Output data
      USER_DRD    : out std_logic_vector(LIMIT_WIDTH+SPEED_WIDTH+CONST_WIDTH-1 downto 0)
   );

end rate_lim_mi32;
