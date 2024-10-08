-- sysmon_ent.vhd
--!
--! @file
--! \brief System monitor with MI32 interface entity
--! \author Lukas Kekely <kekely@cesnet.cz>
--! \date 2012
--!
--! @section License
--!
--! Copyright (C) 2012 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
--! Part of IEEE standard library.
use IEEE.numeric_std.all;

--! \brief System monitor with MI32 interface entity.
--! \details Connects component SYSMON for different FPGAs to MI32 interface.
entity SYSMON_MI32 is
  generic (
    --! \brief Enable sysmon instantion
    SYSMON_EN      : boolean := true
  );
  port (
    --! \name Basic signals

    --! Global clock.
    --! \brief Global clock.
    --! \details For Virtex-5 the clock frequency must be in range from 2 Mhz to 200 MHz. \n
    --! For Virtex-6 the clock frequency must be in range from 2 MHz to 80 MHz. Note that initial 250 MHz maximum has been changed (see http://www.xilinx.com/support/answers/36642.htm).
    CLK            : in std_logic;
    --! Global reset.
    RESET          : in std_logic;

    --! name Sysmon direct signals

    --! Bank select for sysmon
    BANK          : in std_logic_vector(1 downto 0);
    --! Sysmon raised alarm, as programmed by SW
    ALARM         : out std_logic;

    --! \name MI32 interface

    --! Data to write.
    MI_DWR        : in  std_logic_vector(31 downto 0);
    --! Read/write address.
    MI_ADDR       : in  std_logic_vector(31 downto 0);
    --! Read valid.
    MI_RD         : in  std_logic;
    --! Write valid.
    MI_WR         : in  std_logic;
    --! Write data byte enable (not supported).
    MI_BE         : in  std_logic_vector(3 downto 0);
    --! Read data.
    MI_DRD        : out std_logic_vector(31 downto 0);
    --! Read/write address ready.
    MI_ARDY       : out std_logic;
    --! Read data ready.
    MI_DRDY       : out std_logic
  );
end entity;
