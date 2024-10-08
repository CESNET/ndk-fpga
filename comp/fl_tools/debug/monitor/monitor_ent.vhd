--
-- fl_monitor.vhd: Monitors Framelink for certain data at defined position.
-- Copyright (C) 2004 CESNET
-- Author(s): Lukas Solanka <solanka@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use work.math_pack.all;
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity fl_monitor is
   generic (
      -- Framelink data width in bits
      FL_WIDTH : integer;
      -- Monitored word width in bits
      WORD_WIDTH : integer;
      -- Monitored word position - Counts the i'th word (with WORD_WIDTH
      -- width) starting from 0
      WORD_POS : integer
      -- Default data the component is checking for
   );
   port (
      -- ==============
      -- Common signals
      -- ==============

      RESET     : in std_logic;
      CLK       : in std_logic;

      -- This will set default monitored data after RESET
      DEFAULT_DATA : in std_logic_vector(WORD_WIDTH - 1 downto 0);

      -- Framelink interface of transmitting component
      SOF_N     : in std_logic;
      SOP_N     : in std_logic;
      EOP_N     : in std_logic;
      EOF_N     : in std_logic;
      SRC_RDY_N : in std_logic;
      -- This is actually signal from the component that is receiving data
      DST_RDY_N : in std_logic;
      DATA      : in std_logic_vector(FL_WIDTH - 1 downto 0);
      DREM      : in std_logic_vector(log2(FL_WIDTH/8) - 1 downto 0);

      -- ================
      -- Memory interface
      -- ================

      -- Read Request
      ADC_RD         : in    std_logic;
      -- Write Request
      ADC_WR         : in    std_logic;
      -- Address
      ADC_ADDR       : in    std_logic_vector( 7 downto 0);
      -- Input Data
      ADC_DI         : in    std_logic_vector(31 downto 0);
      -- Output Data
      ADC_DO         : out   std_logic_vector(31 downto 0);
      ADC_ARDY       : out   std_logic;
      ADC_DRDY       : out   std_logic
   );
end entity fl_monitor;

