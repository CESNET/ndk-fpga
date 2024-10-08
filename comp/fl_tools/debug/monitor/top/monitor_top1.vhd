--
-- monitor_top1.vhd: FL_MONITOR cover
-- Copyright (C) 2008 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use work.math_pack.all;
use work.fl_pkg.all;
use work.mi32_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FL_MONITOR_TOP1 is
   generic (
      FL_WIDTH    : integer;
      -- Monitored word width in bits
      WORD_WIDTH  : integer;
      -- Monitored word position - Counts the i'th word (with WORD_WIDTH
      -- width) starting from 0
      WORD_POS    : integer
   );
   port (
      -- Common signals
      RESET          : in std_logic;
      CLK            : in std_logic;

      -- This will set default monitored data after RESET
      DEFAULT_DATA   : in std_logic_vector(WORD_WIDTH - 1 downto 0);

      -- Framelink interface of transmitting component
      RX_SOF_N       : in std_logic;
      RX_SOP_N       : in std_logic;
      RX_EOP_N       : in std_logic;
      RX_EOF_N       : in std_logic;
      RX_DATA        : in std_logic_vector(FL_WIDTH - 1 downto 0);
      RX_DREM        : in std_logic_vector(log2(FL_WIDTH/8) - 1 downto 0);
      RX_SRC_RDY_N   : in std_logic;
      RX_DST_RDY_N   : in std_logic;

      -- Memory interface
      MI             : inout t_mi32
   );

end entity FL_MONITOR_TOP1;

architecture full of FL_MONITOR_TOP1 is
begin
   fl_monitor_i : entity work.fl_monitor
      generic map(
         -- Framelink data width in bits
         FL_WIDTH => FL_WIDTH,
         -- Monitored word width in bits
         WORD_WIDTH => WORD_WIDTH,
         -- Monitored word position - Counts the i'th word (with WORD_WIDTH
         -- width) starting from 0
         WORD_POS => WORD_POS
      )
      port map (
         -- Common signals
         RESET     => RESET,
         CLK       => CLK,
         -- This will set default monitored data after RESET
         DEFAULT_DATA => DEFAULT_DATA,

         -- Framelink interface of transmitting component
         SOF_N     => RX_SOF_N,
         SOP_N     => RX_SOP_N,
         EOP_N     => RX_EOP_N,
         EOF_N     => RX_EOF_N,
         SRC_RDY_N => RX_SRC_RDY_N,
         -- This is actually signal from the component that is receiving data
         DST_RDY_N => RX_DST_RDY_N,
         DATA      => RX_DATA,
         DREM      => RX_DREM,

         -- Memory interface
         ADC_RD    => MI.RD,
         ADC_WR    => MI.WR,
         ADC_ADDR  => MI.ADDR(7 downto 0),
         ADC_DI    => MI.DWR,
         ADC_DO    => MI.DRD,
         ADC_ARDY  => MI.ARDY,
         ADC_DRDY  => MI.DRDY
      );

end architecture full;
