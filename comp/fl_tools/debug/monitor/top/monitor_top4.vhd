--
-- monitor_top4_fl16.vhd: 4 FL_MONITORs cover with 16-bit FrameLink interface
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
entity FL_MONITOR_TOP4 is
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
      DEFAULT_DATA0  : in std_logic_vector(WORD_WIDTH - 1 downto 0);
      DEFAULT_DATA1  : in std_logic_vector(WORD_WIDTH - 1 downto 0);
      DEFAULT_DATA2  : in std_logic_vector(WORD_WIDTH - 1 downto 0);
      DEFAULT_DATA3  : in std_logic_vector(WORD_WIDTH - 1 downto 0);

      -- Framelink interface of transmitting component
      RX0_SOF_N      : in std_logic;
      RX0_SOP_N      : in std_logic;
      RX0_EOP_N      : in std_logic;
      RX0_EOF_N      : in std_logic;
      RX0_DATA       : in std_logic_vector(FL_WIDTH - 1 downto 0);
      RX0_DREM       : in std_logic_vector(log2(FL_WIDTH/8) - 1 downto 0);
      RX0_SRC_RDY_N  : in std_logic;
      RX0_DST_RDY_N  : in std_logic;

      RX1_SOF_N      : in std_logic;
      RX1_SOP_N      : in std_logic;
      RX1_EOP_N      : in std_logic;
      RX1_EOF_N      : in std_logic;
      RX1_DATA       : in std_logic_vector(FL_WIDTH - 1 downto 0);
      RX1_DREM       : in std_logic_vector(log2(FL_WIDTH/8) - 1 downto 0);
      RX1_SRC_RDY_N  : in std_logic;
      RX1_DST_RDY_N  : in std_logic;

      RX2_SOF_N      : in std_logic;
      RX2_SOP_N      : in std_logic;
      RX2_EOP_N      : in std_logic;
      RX2_EOF_N      : in std_logic;
      RX2_DATA       : in std_logic_vector(FL_WIDTH - 1 downto 0);
      RX2_DREM       : in std_logic_vector(log2(FL_WIDTH/8) - 1 downto 0);
      RX2_SRC_RDY_N  : in std_logic;
      RX2_DST_RDY_N  : in std_logic;

      RX3_SOF_N      : in std_logic;
      RX3_SOP_N      : in std_logic;
      RX3_EOP_N      : in std_logic;
      RX3_EOF_N      : in std_logic;
      RX3_DATA       : in std_logic_vector(FL_WIDTH - 1 downto 0);
      RX3_DREM       : in std_logic_vector(log2(FL_WIDTH/8) - 1 downto 0);
      RX3_SRC_RDY_N  : in std_logic;
      RX3_DST_RDY_N  : in std_logic;

      -- Memory interface
      MI             : inout t_mi32
   );

end entity FL_MONITOR_TOP4;

architecture full of FL_MONITOR_TOP4 is
   -- ------------------ Signals declaration ----------------------------------
   signal monitor0_sel        : std_logic;
   signal monitor1_sel        : std_logic;
   signal monitor2_sel        : std_logic;
   signal monitor3_sel        : std_logic;

   signal monitor0_adc_do     : std_logic_vector(31 downto 0);
   signal monitor1_adc_do     : std_logic_vector(31 downto 0);
   signal monitor2_adc_do     : std_logic_vector(31 downto 0);
   signal monitor3_adc_do     : std_logic_vector(31 downto 0);

   signal monitor0_ardy      : std_logic;
   signal monitor1_ardy      : std_logic;
   signal monitor2_ardy      : std_logic;
   signal monitor3_ardy      : std_logic;

   signal monitor0_drdy      : std_logic;
   signal monitor1_drdy      : std_logic;
   signal monitor2_drdy      : std_logic;
   signal monitor3_drdy      : std_logic;

   signal monitor0_adc_wr     : std_logic;
   signal monitor1_adc_wr     : std_logic;
   signal monitor2_adc_wr     : std_logic;
   signal monitor3_adc_wr     : std_logic;

   signal monitor0_adc_rd     : std_logic;
   signal monitor1_adc_rd     : std_logic;
   signal monitor2_adc_rd     : std_logic;
   signal monitor3_adc_rd     : std_logic;

begin

   -- select signals
   monitor0_sel  <= '1' when MI.ADDR(9 downto 8) = "00" else '0';
   monitor1_sel  <= '1' when MI.ADDR(9 downto 8) = "01" else '0';
   monitor2_sel  <= '1' when MI.ADDR(9 downto 8) = "10" else '0';
   monitor3_sel  <= '1' when MI.ADDR(9 downto 8) = "11" else '0';

   -- ADC DATA OUT multiplexinig
   MI.DRD     <= monitor0_adc_do when monitor0_sel = '1' else
                 monitor1_adc_do when monitor1_sel = '1' else
                 monitor2_adc_do when monitor2_sel = '1' else
                 monitor3_adc_do;

   MI.ARDY     <= monitor0_ardy when monitor0_sel = '1' else
                  monitor1_ardy when monitor1_sel = '1' else
                  monitor2_ardy when monitor2_sel = '1' else
                  monitor3_ardy;

   MI.DRDY     <= monitor0_drdy when monitor0_sel = '1' else
                  monitor1_drdy when monitor1_sel = '1' else
                  monitor2_drdy when monitor2_sel = '1' else
                  monitor3_drdy;

   -- read request signals
   monitor0_adc_rd  <= MI.RD when monitor0_sel = '1' else '0';
   monitor1_adc_rd  <= MI.RD when monitor1_sel = '1' else '0';
   monitor2_adc_rd  <= MI.RD when monitor2_sel = '1' else '0';
   monitor3_adc_rd  <= MI.RD when monitor3_sel = '1' else '0';

   -- write request
   monitor0_adc_wr  <= MI.WR when monitor0_sel = '1' else '0';
   monitor1_adc_wr  <= MI.WR when monitor1_sel = '1' else '0';
   monitor2_adc_wr  <= MI.WR when monitor2_sel = '1' else '0';
   monitor3_adc_wr  <= MI.WR when monitor3_sel = '1' else '0';

   -- mapping FL_MONITORs -------------------------------------------------------
   fl_monitor0_i : entity work.fl_monitor
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
         DEFAULT_DATA => DEFAULT_DATA0,

         -- Framelink interface of transmitting component
         SOF_N     => RX0_SOF_N,
         SOP_N     => RX0_SOP_N,
         EOP_N     => RX0_EOP_N,
         EOF_N     => RX0_EOF_N,
         SRC_RDY_N => RX0_SRC_RDY_N,
         -- This is actually signal from the component that is receiving data
         DST_RDY_N => RX0_DST_RDY_N,
         DATA      => RX0_DATA,
         DREM      => RX0_DREM,

         -- Memory interface
         ADC_RD    => monitor0_adc_rd,
         ADC_WR    => monitor0_adc_wr,
         ADC_ADDR  => MI.ADDR(7 downto 0),
         ADC_DI    => MI.DWR,
         ADC_DO    => monitor0_adc_do,
         ADC_ARDY  => monitor0_ardy,
         ADC_DRDY  => monitor0_drdy
      );

   fl_monitor1_i : entity work.fl_monitor
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
         DEFAULT_DATA => DEFAULT_DATA1,

         -- Framelink interface of transmitting component
         SOF_N     => RX1_SOF_N,
         SOP_N     => RX1_SOP_N,
         EOP_N     => RX1_EOP_N,
         EOF_N     => RX1_EOF_N,
         SRC_RDY_N => RX1_SRC_RDY_N,
         -- This is actually signal from the component that is receiving data
         DST_RDY_N => RX1_DST_RDY_N,
         DATA      => RX1_DATA,
         DREM      => RX1_DREM,

         -- Memory interface
         ADC_RD    => monitor1_adc_rd,
         ADC_WR    => monitor1_adc_wr,
         ADC_ADDR  => MI.ADDR(7 downto 0),
         ADC_DI    => MI.DWR,
         ADC_DO    => monitor1_adc_do,
         ADC_ARDY  => monitor1_ardy,
         ADC_DRDY  => monitor1_drdy
      );

   fl_monitor2_i : entity work.fl_monitor
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
         DEFAULT_DATA => DEFAULT_DATA2,

         -- Framelink interface of transmitting component
         SOF_N     => RX2_SOF_N,
         SOP_N     => RX2_SOP_N,
         EOP_N     => RX2_EOP_N,
         EOF_N     => RX2_EOF_N,
         SRC_RDY_N => RX2_SRC_RDY_N,
         -- This is actually signal from the component that is receiving data
         DST_RDY_N => RX2_DST_RDY_N,
         DATA      => RX2_DATA,
         DREM      => RX2_DREM,

         -- Memory interface
         ADC_RD    => monitor2_adc_rd,
         ADC_WR    => monitor2_adc_wr,
         ADC_ADDR  => MI.ADDR(7 downto 0),
         ADC_DI    => MI.DWR,
         ADC_DO    => monitor2_adc_do,
         ADC_ARDY  => monitor2_ardy,
         ADC_DRDY  => monitor2_drdy
      );

   fl_monitor3_i : entity work.fl_monitor
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
         DEFAULT_DATA => DEFAULT_DATA3,

         -- Framelink interface of transmitting component
         SOF_N     => RX3_SOF_N,
         SOP_N     => RX3_SOP_N,
         EOP_N     => RX3_EOP_N,
         EOF_N     => RX3_EOF_N,
         SRC_RDY_N => RX3_SRC_RDY_N,
         -- This is actually signal from the component that is receiving data
         DST_RDY_N => RX3_DST_RDY_N,
         DATA      => RX3_DATA,
         DREM      => RX3_DREM,

         -- Memory interface
         ADC_RD    => monitor3_adc_rd,
         ADC_WR    => monitor3_adc_wr,
         ADC_ADDR  => MI.ADDR(7 downto 0),
         ADC_DI    => MI.DWR,
         ADC_DO    => monitor3_adc_do,
         ADC_ARDY  => monitor3_ardy,
         ADC_DRDY  => monitor3_drdy
      );

end architecture full;
